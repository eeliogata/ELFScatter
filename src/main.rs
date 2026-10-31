use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs::{self, File, OpenOptions};
use std::io::{Cursor, Read, Write as _};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use gimli::{
    BaseAddresses, CfaRule, CieOrFde, DebugFrame, EhFrame, EhFrameOffset, LittleEndian,
    RegisterRule, UnwindContext, UnwindSection,
};
use iced_x86::{
    BlockEncoder, BlockEncoderOptions, ConditionCode, Decoder, DecoderOptions, FlowControl,
    Instruction, InstructionBlock, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
};
use lief::elf::dynamic::DynamicEntry as _;
use lief::elf::{self, dynamic, header, relocation, section, segment, symbol};
use lief::generic::{Binary as _, Relocation as _, Section as _, Symbol as _};

#[derive(Debug)]
enum Error {
    Unsupported(String),
    InvalidInput(String),
    Io(String),
    Invariant(String),
}

impl Error {
    fn category(&self) -> &'static str {
        match self {
            Self::Unsupported(_) => "unsupported input",
            Self::InvalidInput(_) => "invalid input",
            Self::Io(_) => "I/O error",
            Self::Invariant(_) => "internal invariant",
        }
    }

    fn eligibility(self) -> Self {
        match self {
            Self::InvalidInput(message) => Self::Unsupported(message),
            other => other,
        }
    }

    fn invariant(self) -> Self {
        Self::Invariant(self.to_string())
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(message)
            | Self::InvalidInput(message)
            | Self::Io(message)
            | Self::Invariant(message) => f.write_str(message),
        }
    }
}

impl From<&str> for Error {
    fn from(message: &str) -> Self {
        Self::InvalidInput(message.into())
    }
}

impl From<String> for Error {
    fn from(message: String) -> Self {
        Self::InvalidInput(message)
    }
}

impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error.to_string())
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
struct Options {
    inspect: bool,
    no_vm: bool,
    keep_metadata: bool,
    startup_smc: bool,
    scrub: Scrub,
    input: PathBuf,
    output: Option<PathBuf>,
    map: Option<PathBuf>,
    symbols: Vec<String>,
    exclude: BTreeSet<String>,
    address: Option<u64>,
    size: Option<u64>,
    seed: Option<u64>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Scrub {
    Trap,
    Random,
    Off,
}

const HELP: &str = "Usage: elfscatter INPUT OUTPUT [options]
       elfscatter rewrite INPUT -o OUTPUT [options]
       elfscatter inspect INPUT [selection, mode, and seed options]

Selection: --symbol NAME (repeatable), --exclude NAME (automatic selection),
           --address VA --size BYTES
Mode:      --no-vm (routes only)
Seed:      --seed N
Rewrite:   --scrub trap|random|off, --map FILE,
           --keep-metadata, --no-startup-smc
General:   --help, --version

Mixed stack/register VMs and startup decoding are enabled by default.
Unsupported functions use strong/layout routes.
";

enum Action {
    Help,
    Version,
    Run(Options),
}

fn parse(args: impl IntoIterator<Item = String>) -> Result<Action> {
    let args: Vec<_> = args.into_iter().collect();
    if args.iter().any(|s| s == "--help" || s == "-h") {
        return Ok(Action::Help);
    }
    if args.len() == 1 && args[0] == "--version" {
        return Ok(Action::Version);
    }
    parse_options(args.into_iter()).map(Action::Run)
}

fn parse_number(s: &str) -> Result<u64> {
    if let Some(hex) = s.strip_prefix("0x") {
        u64::from_str_radix(hex, 16)
            .map_err(|_| Error::InvalidInput(format!("invalid number: {s}")))
    } else {
        s.parse::<u64>()
            .map_err(|_| Error::InvalidInput(format!("invalid number: {s}")))
    }
}

fn parse_options(mut args: impl Iterator<Item = String>) -> Result<Options> {
    let first = args
        .next()
        .ok_or("usage: elfscatter INPUT OUTPUT [options] | elfscatter inspect INPUT [options]")?;
    let (inspect, input, output) = match first.as_str() {
        "inspect" => (
            true,
            PathBuf::from(args.next().ok_or("missing input ELF")?),
            None,
        ),
        "rewrite" => (
            false,
            PathBuf::from(args.next().ok_or("missing input ELF")?),
            None,
        ),
        _ => (
            false,
            PathBuf::from(first),
            Some(PathBuf::from(args.next().ok_or("missing output ELF")?)),
        ),
    };
    let positional_output = output.is_some();
    let mut opts = Options {
        inspect,
        no_vm: false,
        keep_metadata: false,
        startup_smc: true,
        scrub: Scrub::Trap,
        input,
        output,
        map: None,
        symbols: Vec::new(),
        exclude: BTreeSet::new(),
        address: None,
        size: None,
        seed: None,
    };
    while let Some(arg) = args.next() {
        if arg == "--vm" {
            return Err(
                "--vm was removed: VM execution is now the default; omit this option".into(),
            );
        }
        if matches!(arg.as_str(), "--strong-only" | "--no-dispatch") {
            return Err(format!(
                "{arg} was removed: use --no-vm for automatic strong/layout routing"
            )
            .into());
        }
        if arg == "--no-vm" {
            opts.no_vm = true;
            continue;
        }
        if arg == "--keep-metadata" {
            opts.keep_metadata = true;
            continue;
        }
        if arg == "--no-startup-smc" {
            opts.startup_smc = false;
            continue;
        }
        if inspect && arg == "--scrub" {
            return Err("--scrub applies only to rewrite".into());
        }
        if !matches!(
            arg.as_str(),
            "--symbol"
                | "--exclude"
                | "--address"
                | "--size"
                | "--seed"
                | "--scrub"
                | "--map"
                | "-o"
                | "--output"
        ) {
            return Err(format!("unknown option: {arg}").into());
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {arg}"))?;
        match arg.as_str() {
            "--symbol" => opts.symbols.push(value),
            "--exclude" => {
                opts.exclude.insert(value);
            }
            "--address" => opts.address = Some(parse_number(&value)?),
            "--size" => opts.size = Some(parse_number(&value)?),
            "--seed" => opts.seed = Some(parse_number(&value)?),
            "--scrub" => {
                opts.scrub = match value.as_str() {
                    "trap" => Scrub::Trap,
                    "random" => Scrub::Random,
                    "off" => Scrub::Off,
                    _ => return Err("--scrub must be trap, random, or off".into()),
                }
            }
            "--map" => opts.map = Some(PathBuf::from(value)),
            "-o" | "--output" if positional_output => return Err("output specified twice".into()),
            "-o" | "--output" => opts.output = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown option: {arg}").into()),
        }
    }
    if opts.address.is_some() != opts.size.is_some() {
        return Err("--address requires --size".into());
    }
    if opts.address.is_some() && (!opts.symbols.is_empty() || !opts.exclude.is_empty()) {
        return Err("cannot mix address selection with symbols or exclusions".into());
    }
    if !opts.symbols.is_empty() && !opts.exclude.is_empty() {
        return Err("--exclude applies only to automatic selection".into());
    }
    if inspect {
        if opts.output.is_some() || opts.map.is_some() || opts.keep_metadata || !opts.startup_smc {
            return Err("inspect accepts only selection, mode, and seed options".into());
        }
    } else if opts.output.is_none() {
        return Err("rewrite requires -o OUTPUT".into());
    }
    Ok(opts)
}

fn validate_paths(opts: &Options) -> Result<()> {
    if let Some(output) = &opts.output {
        if output.exists() || output == &opts.input {
            return Err("output already exists".into());
        }
        if opts.map.as_ref() == Some(output) || opts.map.as_ref() == Some(&opts.input) {
            return Err("map path conflicts with ELF path".into());
        }
    }
    if opts.map.as_ref().is_some_and(|p| p.exists()) {
        return Err("map already exists".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        Action, Error, FileMapping, FrameRegion, FrameRegisterRule, Scrub, UnwindRule,
        debug_frame_payload, file_range, mapped_range, mask_startup_code, parse, permute_all,
        publish, random_seed, rel32, scrub_bytes, startup_key, validate_elf_bytes,
    };
    use gimli::{
        BaseAddresses, CfaRule, CieOrFde, DebugFrame, LittleEndian, UnwindContext, UnwindSection,
    };
    use std::collections::{BTreeMap, BTreeSet};
    use std::os::unix::fs::PermissionsExt;
    fn options(args: &[&str]) -> super::Options {
        match parse(args.iter().map(|s| s.to_string())).unwrap() {
            Action::Run(options) => options,
            _ => panic!("expected run options"),
        }
    }
    #[test]
    fn vm_is_default() {
        assert!(!options(&["in", "out"]).no_vm);
        assert!(!options(&["inspect", "in"]).no_vm);
        assert!(options(&["in", "out", "--no-vm"]).no_vm);
        assert_eq!(options(&["inspect", "in", "--seed", "0"]).seed, Some(0));
        for flag in ["--vm", "--strong-only", "--no-dispatch", "--vm-arch"] {
            assert!(parse(["in", "out", flag].map(str::to_string)).is_err());
        }
    }
    #[test]
    fn inspect_rejects_rewrite_options() {
        for args in [
            vec!["--no-startup-smc"],
            vec!["--keep-metadata"],
            vec!["--scrub", "off"],
        ] {
            let mut input = vec!["inspect", "in"];
            input.extend(args);
            assert!(parse(input.into_iter().map(str::to_string)).is_err());
        }
        assert!(options(&["inspect", "in", "--no-vm"]).no_vm);
    }
    #[test]
    fn help_and_version_need_no_input() {
        assert!(matches!(parse(["--help".into()]), Ok(Action::Help)));
        assert!(matches!(parse(["--version".into()]), Ok(Action::Version)));
    }
    #[test]
    fn selectors_and_numbers() {
        let o = options(&[
            "rewrite",
            "in",
            "-o",
            "out",
            "--address",
            "0xffff",
            "--size",
            "16",
            "--seed",
            "18446744073709551615",
        ]);
        assert_eq!(o.address, Some(65535));
        assert_eq!(o.seed, Some(u64::MAX));
        for args in [
            vec!["--address", "1"],
            vec!["--seed", "18446744073709551616"],
            vec!["--symbol", "f", "--exclude", "g"],
        ] {
            let mut input = vec!["in", "out"];
            input.extend(args);
            assert!(parse(input.into_iter().map(str::to_string)).is_err());
        }
    }

    #[test]
    fn table_bases_require_agreement_at_joins_and_entries() {
        use iced_x86::{Decoder, DecoderOptions, Register};
        let code = [
            0x4c, 0x8d, 0x25, 0x00, 0x01, 0, 0, // lea r12, [rip + 256]
            0x85, 0xff, 0x74, 0x07, // test edi, edi; je join
            0x4c, 0x8d, 0x25, 0xf5, 0, 0, 0, // lea r12, [same table]
            0x90, 0xc3, // join: nop; ret
        ];
        let mut instructions: Vec<_> = Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE)
            .into_iter()
            .collect();
        let mut edges = vec![vec![1], vec![2], vec![3, 4], vec![4], vec![5], vec![]];
        let states = super::table_base_states(&instructions, &edges, &[0], Register::R12);
        assert_eq!(states[4], Some(0x1107));
        // An additional dispatch edge back to the guard must not lose a valid base.
        edges[4].push(2);
        assert_eq!(
            super::table_base_states(&instructions, &edges, &[0], Register::R12)[4],
            Some(0x1107)
        );
        assert_eq!(
            super::table_base_states(&instructions, &edges, &[0, 4], Register::R12)[4],
            None
        );
        instructions[3].set_memory_displacement64(0x2200);
        assert_eq!(
            super::table_base_states(&instructions, &edges, &[0], Register::R12)[4],
            None
        );
    }

    #[test]
    fn table_bases_follow_call_clobbers_and_partial_writes() {
        use iced_x86::{Decoder, DecoderOptions, Register};
        for (lea, register, preserved) in [
            (&[0x4c, 0x8d, 0x25, 0, 1, 0, 0][..], Register::R12, true),
            (&[0x48, 0x8d, 0x05, 0, 1, 0, 0][..], Register::RAX, false),
        ] {
            let mut code = lea.to_vec();
            code.extend_from_slice(&[0xe8, 0, 0x20, 0, 0, 0xc3]); // call external; ret
            let mut instructions: Vec<_> =
                Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE)
                    .into_iter()
                    .collect();
            let edges = vec![vec![1], vec![2], vec![]];
            assert_eq!(
                super::table_base_states(&instructions, &edges, &[0], register)[2],
                preserved.then_some(0x1107)
            );
            instructions[1].set_near_branch64(0x1000);
            assert_eq!(
                super::table_base_states(&instructions, &edges, &[0], register)[2],
                None
            );
        }
        for update in [
            &[0x66, 0x41, 0xbc, 0, 0][..],
            &[0x49, 0x0f, 0x44, 0xc4][..],
            &[0x4c, 0x0f, 0x44, 0xe0][..],
        ] {
            let mut code = vec![0x4c, 0x8d, 0x25, 0, 1, 0, 0];
            code.extend_from_slice(update);
            code.push(0xc3);
            let instructions: Vec<_> = Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE)
                .into_iter()
                .collect();
            let states = super::table_base_states(
                &instructions,
                &[vec![1], vec![2], vec![]],
                &[0],
                Register::R12,
            );
            // CMOV into RAX only reads R12; the other forms modify it.
            assert_eq!(
                states[2],
                if update == [0x49, 0x0f, 0x44, 0xc4] {
                    Some(0x1107)
                } else {
                    None
                }
            );
        }
    }

    #[test]
    fn relative_dispatch_flags_must_be_overwritten_before_use() {
        use iced_x86::{Decoder, DecoderOptions};
        for (tail, expected) in [
            (&[0x31, 0xc9, 0x11, 0xc0, 0xc3][..], true), // xor ecx,ecx; adc eax,eax; ret
            (&[0xff, 0xc1, 0x11, 0xc0, 0xc3][..], false), // inc ecx leaves carry live
            (&[0xd3, 0xe0, 0x11, 0xc0, 0xc3][..], false), // shl eax,cl may preserve carry
            (&[0xc1, 0xe0, 0x00, 0x11, 0xc0, 0xc3][..], false), // zero immediate count
            (&[0xd1, 0xe0, 0x11, 0xc0, 0xc3][..], true), // nonzero shift overwrites carry
            (&[0xf3, 0xa6, 0x11, 0xc0, 0xc3][..], false), // repe cmpsb may do no work
            (&[0xc3][..], true),                         // arithmetic flags are not ABI results
            (&[0xe8, 0, 0x20, 0, 0, 0x11, 0xc0, 0xc3][..], true), // external call clobbers flags
            (&[0xe8, 0xf6, 0xff, 0xff, 0xff, 0xc3][..], false), // internal call
        ] {
            let mut code = vec![0x48, 0x01, 0xd0, 0xff, 0xe0]; // add rax,rdx; jmp rax
            code.extend_from_slice(tail);
            let instructions: Vec<_> = Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE)
                .into_iter()
                .collect();
            let edges: Vec<_> = (0..instructions.len())
                .map(|i| {
                    if i + 1 < instructions.len() {
                        vec![i + 1]
                    } else {
                        vec![]
                    }
                })
                .collect();
            assert_eq!(super::table_flags_dead(&instructions, &edges, 1), expected);
        }
    }

    #[test]
    fn table_flags_follow_all_dispatch_targets() {
        use iced_x86::{Decoder, DecoderOptions};
        let code = [
            0x48, 0x01, 0xd0, 0xff, 0xe0, // add rax,rdx; jmp rax
            0x31, 0xc9, 0xeb, 0x02, // xor ecx,ecx; jmp join
            0xff, 0xe2, // second dispatch: jmp rdx
            0x11, 0xc0, 0xc3, // join: adc eax,eax; ret
        ];
        let instructions: Vec<_> = Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE)
            .into_iter()
            .collect();
        let mut indirect = BTreeMap::from([(0x1003, vec![0x1005, 0x1009]), (0x1009, vec![0x100b])]);
        let edges = super::table_successors(&instructions, &indirect).unwrap();
        assert!(!super::table_flags_dead(&instructions, &edges, 1));
        indirect.insert(0x1009, vec![0x1005]);
        let edges = super::table_successors(&instructions, &indirect).unwrap();
        assert!(super::table_flags_dead(&instructions, &edges, 1));
        indirect.remove(&0x1009);
        assert!(super::table_successors(&instructions, &indirect).is_err());
    }

    #[test]
    fn relative_dispatch_requires_full_width_addresses() {
        use iced_x86::{Decoder, DecoderOptions};
        for (code, expected) in [
            (
                &[0x48, 0x63, 0x04, 0xba, 0x48, 0x01, 0xd0, 0xff, 0xe0][..],
                true,
            ),
            (&[0x63, 0x04, 0xba, 0x48, 0x01, 0xd0, 0xff, 0xe0][..], false),
            (&[0x48, 0x63, 0x04, 0xba, 0x01, 0xd0, 0xff, 0xe0][..], false),
            (
                &[0x67, 0x48, 0x63, 0x04, 0xba, 0x48, 0x01, 0xd0, 0xff, 0xe0][..],
                false,
            ),
        ] {
            let instructions: Vec<_> = Decoder::with_ip(64, code, 0x1000, DecoderOptions::NONE)
                .into_iter()
                .collect();
            assert_eq!(instructions.len(), 3);
            assert_eq!(
                super::relative_dispatch(&instructions[0], &instructions[1], &instructions[2]),
                expected
            );
        }
    }

    #[test]
    fn ranges_reject_overflow_and_truncation() {
        assert_eq!(file_range(16, 8, 8).unwrap(), 8..16);
        assert_eq!(file_range(16, 16, 0).unwrap(), 16..16);
        assert!(file_range(16, 8, 9).is_err());
        assert!(file_range(16, u64::MAX, 2).is_err());
        assert!(file_range(16, 17, 0).is_err());
    }

    #[test]
    fn load_mapping_must_be_unambiguous() {
        let first = FileMapping {
            address: 0x1000,
            offset: 16,
            size: 64,
        };
        assert_eq!(mapped_range([first], 0x1010, 8, 128).unwrap(), 32..40);
        let overlap = FileMapping {
            address: 0x1014,
            offset: 80,
            size: 16,
        };
        assert!(mapped_range([first, overlap], 0x1010, 8, 128).is_err());
        assert!(mapped_range([overlap, first], 0x1010, 8, 128).is_err());
        assert!(mapped_range([first, first], 0x1010, 8, 128).is_err());
        assert!(mapped_range([first], 0x1038, 16, 128).is_err());
        assert!(mapped_range([first], 0x1010, 8, 36).is_err());
    }

    fn small_elf() -> Vec<u8> {
        let mut bytes = vec![0; 512];
        bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (offset, word) in [(16, 2u16), (18, 62), (52, 64), (54, 56), (56, 2)] {
            bytes[offset..offset + 2].copy_from_slice(&word.to_le_bytes());
        }
        bytes[20..24].copy_from_slice(&1u32.to_le_bytes());
        bytes[64..68].copy_from_slice(&1u32.to_le_bytes());
        bytes[120..124].copy_from_slice(&2u32.to_le_bytes());
        for (offset, word) in [
            (32, 64u64),
            (80, 0x400000),
            (96, 512),
            (104, 512),
            (128, 256),
            (136, 0x400100),
            (152, 64),
            (160, 64),
            (256, 32),
            (264, 0x400180),
            (272, 33),
            (280, 8),
        ] {
            bytes[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
        }
        bytes
    }

    #[test]
    fn elf_tables_are_checked_before_parsing() {
        let bytes = small_elf();
        validate_elf_bytes(&bytes).unwrap();
        for length in [0, 63, 100, 511] {
            assert!(validate_elf_bytes(&bytes[..length]).is_err());
        }
        for (offset, word) in [
            (32, u64::MAX),
            (96, 513),
            (264, u64::MAX),
            (280, 7),
            (288, 32),
        ] {
            let mut malformed = bytes.clone();
            malformed[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
            assert!(validate_elf_bytes(&malformed).is_err(), "offset {offset}");
        }
    }

    #[test]
    fn relative_branches_accept_only_signed_32_bit_displacements() {
        let base = 0x1_0000_0000;
        assert_eq!(
            rel32(base, base + i32::MAX as u64).unwrap(),
            i32::MAX.to_le_bytes()
        );
        assert_eq!(
            rel32(base, base - (1 << 31)).unwrap(),
            i32::MIN.to_le_bytes()
        );
        assert!(rel32(base, base + (1 << 31)).is_err());
        assert!(rel32(base, base - (1 << 31) - 1).is_err());
    }

    #[test]
    fn seeds_replay_layout_and_scrubbing() {
        for seed in [0, 1, u64::MAX] {
            let order = permute_all(97, seed);
            assert_eq!(order, permute_all(97, seed));
            assert_eq!(
                order.iter().copied().collect::<BTreeSet<_>>(),
                (0..97).collect()
            );
            assert_eq!(
                scrub_bytes(Scrub::Random, 256, seed),
                scrub_bytes(Scrub::Random, 256, seed)
            );
        }
        assert_ne!(permute_all(97, 0), permute_all(97, 1));
        assert_ne!(
            scrub_bytes(Scrub::Random, 256, 0),
            scrub_bytes(Scrub::Random, 256, 1)
        );
    }

    #[test]
    fn startup_encoding_round_trips_code() {
        let code: Vec<_> = (0..4096).map(|n| (n * 37) as u8).collect();
        for seed in [0, 1, u64::MAX] {
            let mut encoded = code.clone();
            mask_startup_code(&mut encoded, startup_key(seed)).unwrap();
            assert_ne!(encoded, code);
            mask_startup_code(&mut encoded, startup_key(seed)).unwrap();
            assert_eq!(encoded, code);
            let mut repeated = [0; 24];
            mask_startup_code(&mut repeated, startup_key(seed)).unwrap();
            assert_ne!(repeated[..8], repeated[8..16]);
            assert_ne!(repeated[8..16], repeated[16..24]);
        }
    }

    #[test]
    fn emitted_cfi_changes_at_instruction_boundaries() {
        let entry = UnwindRule {
            cfa_register: 7,
            cfa_offset: 8,
            cfa_expression: None,
            registers: BTreeMap::from([(16, FrameRegisterRule::Offset(-8))]),
        };
        let mut saved = entry.clone();
        saved.cfa_offset = 16;
        saved.registers.insert(6, FrameRegisterRule::Offset(-16));
        let bytes = debug_frame_payload(
            &[FrameRegion {
                va: 0x401000,
                len: 4,
                rows: vec![(0, entry.clone()), (1, saved), (3, entry)],
            }],
            0,
        )
        .unwrap();
        let frame = DebugFrame::new(&bytes, LittleEndian);
        let bases = BaseAddresses::default();
        let mut entries = frame.entries(&bases);
        assert!(matches!(entries.next().unwrap(), Some(CieOrFde::Cie(_))));
        let Some(CieOrFde::Fde(partial)) = entries.next().unwrap() else {
            panic!("missing FDE")
        };
        let fde = partial
            .parse(|section, bases, offset| section.cie_from_offset(bases, offset))
            .unwrap();
        let mut context = UnwindContext::new();
        let mut table = fde.rows(&frame, &bases, &mut context).unwrap();
        let mut rows = Vec::new();
        while let Some(row) = table.next_row().unwrap() {
            let CfaRule::RegisterAndOffset { register, offset } = row.cfa() else {
                panic!("unexpected CFA")
            };
            rows.push((row.start_address(), register.0, *offset));
        }
        assert_eq!(
            rows,
            [(0x401000, 7, 8), (0x401001, 7, 16), (0x401003, 7, 8)]
        );
    }

    #[test]
    fn publication_preserves_existing_outputs_and_rolls_back() {
        let directory =
            std::env::temp_dir().join(format!("elfscatter-publish-{:x}", random_seed().unwrap()));
        std::fs::create_dir(&directory).unwrap();
        let output = directory.join("output");
        let map = directory.join("map");
        std::fs::write(&map, b"original map").unwrap();
        assert!(
            publish(
                b"new ELF",
                &output,
                std::fs::Permissions::from_mode(0o755),
                Some((&map, b"new map"))
            )
            .is_err()
        );
        assert!(!output.exists());
        assert_eq!(std::fs::read(&map).unwrap(), b"original map");
        publish(
            b"first ELF",
            &output,
            std::fs::Permissions::from_mode(0o755),
            None,
        )
        .unwrap();
        assert!(
            publish(
                b"second ELF",
                &output,
                std::fs::Permissions::from_mode(0o755),
                None
            )
            .is_err()
        );
        assert_eq!(std::fs::read(&output).unwrap(), b"first ELF");
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 2);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn eligibility_does_not_hide_internal_failures() {
        assert!(matches!(
            Error::InvalidInput("unsupported form".into()).eligibility(),
            Error::Unsupported(_)
        ));
        assert!(matches!(
            Error::Invariant("missing plan".into()).eligibility(),
            Error::Invariant(_)
        ));
        assert!(matches!(
            Error::Io("read failed".into()).eligibility(),
            Error::Io(_)
        ));
    }
}

#[derive(Clone, Copy)]
enum Exit {
    Branch {
        target: u64,
        fallthrough: u64,
        cc: ConditionCode,
    },
    Jump(u64),
    Return,
    Fallthrough(u64),
    Table(usize),
    Dispatch(usize),
}

struct Block {
    old: u64,
    body: Vec<Instruction>,
    exit: Exit,
    len: usize,
}

struct Function {
    start: u64,
    end: u64,
    bytes: Vec<u8>,
    entries: Vec<EntryPatch>,
    blocks: Vec<Block>,
    tables: Vec<JumpTable>,
    dispatches: Vec<IndexedDispatch>,
    fixed_targets: Vec<u64>,
    fixed_slots: Vec<u64>,
    unwind: Option<Vec<(u64, UnwindRule)>>,
}

struct IndexedDispatch {
    jump: Instruction,
    guard: u64,
    targets: Vec<u64>,
    index: Register,
    notrack: bool,
    original_base: u64,
    original_bytes: Vec<u8>,
}

struct EntryPatch {
    label: u64,
    window: Option<(u64, usize)>,
    sources: Vec<SourcePatch>,
}

struct SourcePatch {
    source: u64,
    address: u64,
    next: u64,
    original: [u8; 4],
}

struct JumpTable {
    lea: u64,
    jump: u64,
    guard: u64,
    targets: Vec<u64>,
    setup: Option<TableSetup>,
    kind: TableKind,
    original_base: u64,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TableKind {
    Relative,
    Absolute,
}

#[derive(Clone, Copy)]
struct TableSetup {
    load: u64,
    register: Register,
    original: u64,
}

impl JumpTable {
    fn width(&self) -> usize {
        match self.kind {
            TableKind::Relative => 4,
            TableKind::Absolute => 8,
        }
    }

    fn unique(&self) -> Vec<u64> {
        self.targets
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    fn internal_unique(&self, function: &Function) -> Vec<u64> {
        self.unique()
            .into_iter()
            .filter(|&target| in_range(target, function.start, function.end))
            .collect()
    }
}

#[derive(Clone, PartialEq, Eq)]
struct UnwindRule {
    cfa_register: u16,
    cfa_offset: i32,
    cfa_expression: Option<Vec<u8>>,
    registers: BTreeMap<u16, FrameRegisterRule>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FrameRegisterRule {
    Undefined,
    SameValue,
    Offset(i32),
    ValOffset(i32),
    Register(u16),
    Expression(Vec<u8>),
}

struct FrameRange {
    start: u64,
    end: u64,
    offset: usize,
    unsupported: bool,
}

struct Candidate {
    start: u64,
    size: u64,
    names: BTreeSet<String>,
}

struct Selected {
    candidate: Candidate,
    function: Function,
    plan: Plan,
    vm_reason: Option<String>,
}

enum Plan {
    Vm(vm::VmPlan),
    Strong(Scratch),
    Layout,
}

impl Selected {
    fn mode(&self) -> Mode {
        match self.plan {
            Plan::Vm(_) => Mode::Vm,
            Plan::Strong(_) => Mode::Strong,
            Plan::Layout => Mode::Layout,
        }
    }

    fn scratch(&self) -> Scratch {
        match self.plan {
            Plan::Strong(scratch) => scratch,
            _ => Scratch::default(),
        }
    }

    fn vm(&self) -> Option<&vm::VmPlan> {
        match &self.plan {
            Plan::Vm(plan) => Some(plan),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Default)]
struct Scratch {
    r10: Option<u8>,
    r11: Option<u8>,
    state: Option<u8>,
    rcx: Option<u8>,
}

impl Scratch {
    fn saved(self) -> usize {
        usize::from(self.r10.is_some())
            + usize::from(self.r11.is_some())
            + usize::from(self.rcx.is_some())
    }

    fn entry_len(self) -> usize {
        19 + self.saved() * 5
    }

    fn prefix_len(self) -> usize {
        (self.saved() + usize::from(self.state.is_some())) * 5
    }

    fn route_len(self) -> usize {
        self.prefix_len()
    }

    fn reset_len(self) -> usize {
        (if self.state.is_some() { 25 } else { 10 })
            + (usize::from(self.r10.is_some()) + usize::from(self.rcx.is_some())) * 5
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Mode {
    Vm,
    Strong,
    Layout,
}

struct Skipped {
    address: u64,
    reason: String,
}

fn main() -> ExitCode {
    let result = parse(env::args().skip(1)).and_then(|action| match action {
        Action::Help => Ok(HELP.to_string()),
        Action::Version => Ok(format!("elfscatter {}\n", env!("CARGO_PKG_VERSION"))),
        Action::Run(opts) => run(opts),
    });
    match result {
        Ok(report) => match std::io::stdout().lock().write_all(report.as_bytes()) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => ExitCode::SUCCESS,
            Err(e) => {
                let _ = writeln!(std::io::stderr(), "elfscatter: {e}");
                ExitCode::FAILURE
            }
        },
        Err(err) => {
            let _ = writeln!(std::io::stderr(), "elfscatter: {}: {err}", err.category());
            ExitCode::FAILURE
        }
    }
}

struct Snapshot {
    bytes: Vec<u8>,
    permissions: fs::Permissions,
}

impl Snapshot {
    fn read(path: &Path) -> Result<Self> {
        let mut file = File::open(path)?;
        let before = file.metadata()?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)?;
        let after = file.metadata()?;
        if bytes.len() as u64 != before.len()
            || before.len() != after.len()
            || before.modified()? != after.modified()?
        {
            return Err("input changed while being read".into());
        }
        Ok(Self {
            bytes,
            permissions: before.permissions(),
        })
    }
}

fn file_range(length: usize, offset: u64, size: u64) -> Result<std::ops::Range<usize>> {
    let end = offset.checked_add(size).ok_or("ELF file range overflow")?;
    if end > length as u64 {
        return Err("truncated ELF data".into());
    }
    Ok(
        usize::try_from(offset).map_err(|_| "ELF offset out of range")?
            ..usize::try_from(end).map_err(|_| "ELF offset out of range")?,
    )
}

fn elf_u16(bytes: &[u8], offset: usize) -> Result<u16> {
    Ok(u16::from_le_bytes(
        bytes[file_range(bytes.len(), offset as u64, 2)?]
            .try_into()
            .unwrap(),
    ))
}

fn elf_u32(bytes: &[u8], offset: usize) -> Result<u32> {
    Ok(u32::from_le_bytes(
        bytes[file_range(bytes.len(), offset as u64, 4)?]
            .try_into()
            .unwrap(),
    ))
}

fn elf_u64(bytes: &[u8], offset: usize) -> Result<u64> {
    Ok(u64::from_le_bytes(
        bytes[file_range(bytes.len(), offset as u64, 8)?]
            .try_into()
            .unwrap(),
    ))
}

#[derive(Clone, Copy)]
struct FileMapping {
    address: u64,
    offset: u64,
    size: u64,
}

fn mapped_range(
    mappings: impl IntoIterator<Item = FileMapping>,
    address: u64,
    size: u64,
    file_len: usize,
) -> Result<std::ops::Range<usize>> {
    let end = address
        .checked_add(size)
        .ok_or("ELF address range overflow")?;
    let mut found = None;
    for mapping in mappings {
        let limit = mapping
            .address
            .checked_add(mapping.size)
            .ok_or("ELF segment overflow")?;
        if address < limit && end > mapping.address {
            if address < mapping.address || end > limit || found.is_some() {
                return Err("ambiguous ELF load mapping".into());
            }
            let offset = mapping
                .offset
                .checked_add(address - mapping.address)
                .ok_or("ELF file offset overflow")?;
            found = Some(file_range(file_len, offset, size)?);
        }
    }
    found.ok_or_else(|| Error::InvalidInput(format!("unmapped ELF data at 0x{address:x}")))
}

fn header_entry(bytes: &[u8], section: bool, index: usize) -> Result<usize> {
    let (offset, stride, count, expected) = if section {
        (40, 58, 60, 64)
    } else {
        (32, 54, 56, 56)
    };
    if elf_u16(bytes, stride)? != expected || index >= elf_u16(bytes, count)? as usize {
        return Err("invalid ELF header table entry".into());
    }
    let at = elf_u64(bytes, offset)?
        .checked_add(index as u64 * u64::from(expected))
        .ok_or("ELF header table overflow")?;
    Ok(file_range(bytes.len(), at, u64::from(expected))?.start)
}

fn validate_elf_bytes(bytes: &[u8]) -> Result<()> {
    if bytes.len() < 64
        || bytes.get(..7) != Some(b"\x7fELF\x02\x01\x01")
        || elf_u16(bytes, 18)? != 62
        || !matches!(elf_u16(bytes, 16)?, 2 | 3)
        || elf_u32(bytes, 20)? != 1
        || elf_u16(bytes, 52)? != 64
    {
        return Err("requires an ELF64 little-endian x86-64 executable".into());
    }
    let phnum = elf_u16(bytes, 56)? as usize;
    let shnum = elf_u16(bytes, 60)? as usize;
    if phnum == 0 || phnum == 0xffff || (shnum == 0 && elf_u64(bytes, 40)? != 0) {
        return Err("unsupported ELF header counts".into());
    }
    let mut loads = Vec::new();
    let mut load_ranges = Vec::new();
    let mut dynamic = None;
    let mut singleton_segments = BTreeSet::new();
    for i in 0..phnum {
        let at = header_entry(bytes, false, i)?;
        let kind = elf_u32(bytes, at)?;
        let offset = elf_u64(bytes, at + 8)?;
        let address = elf_u64(bytes, at + 16)?;
        let size = elf_u64(bytes, at + 32)?;
        let memory = elf_u64(bytes, at + 40)?;
        let range = file_range(bytes.len(), offset, size)?;
        address
            .checked_add(memory)
            .ok_or("ELF segment address overflow")?;
        if matches!(kind, 2 | 3 | 6 | 0x6474e550) && !singleton_segments.insert(kind) {
            return Err("duplicate ELF loader segment".into());
        }
        if kind == 1 {
            if size > memory {
                return Err("ELF segment file size exceeds memory size".into());
            }
            let end = address
                .checked_add(memory)
                .ok_or("ELF segment address overflow")?;
            if memory != 0
                && load_ranges
                    .iter()
                    .any(|&(start, stop)| address < stop && end > start)
            {
                return Err("overlapping ELF load segments".into());
            }
            if memory != 0 {
                load_ranges.push((address, end));
            }
            loads.push(FileMapping {
                address,
                offset,
                size,
            });
        } else if kind == 2 {
            dynamic = Some(range);
        } else if kind == 3 && (size == 0 || bytes[range.end - 1] != 0) {
            return Err("invalid ELF interpreter".into());
        }
    }
    for i in 0..shnum {
        let at = header_entry(bytes, true, i)?;
        let kind = elf_u32(bytes, at + 4)?;
        let size = elf_u64(bytes, at + 32)?;
        if kind != 8 {
            file_range(bytes.len(), elf_u64(bytes, at + 24)?, size)?;
        }
        elf_u64(bytes, at + 16)?
            .checked_add(size)
            .ok_or("ELF section address overflow")?;
        if elf_u32(bytes, at + 40)? as usize >= shnum {
            return Err("invalid ELF section link".into());
        }
        let entry = match kind {
            2 | 4 | 11 => Some(24),
            6 | 9 => Some(16),
            _ => None,
        };
        if let Some(entry) = entry
            && (elf_u64(bytes, at + 56)? != entry || size % entry != 0)
        {
            return Err("invalid ELF section entry size".into());
        }
    }
    let names = elf_u16(bytes, 62)? as usize;
    if names != 0 {
        let at = header_entry(bytes, true, names)?;
        if elf_u32(bytes, at + 4)? != 3 {
            return Err("invalid ELF section-name table".into());
        }
        let strings = &bytes[file_range(
            bytes.len(),
            elf_u64(bytes, at + 24)?,
            elf_u64(bytes, at + 32)?,
        )?];
        for i in 0..shnum {
            let name = elf_u32(bytes, header_entry(bytes, true, i)?)? as usize;
            if strings.get(name..).is_none_or(|tail| !tail.contains(&0)) {
                return Err("invalid ELF section name".into());
            }
        }
    }
    if let Some(range) = dynamic {
        if range.len() % 16 != 0 {
            return Err("truncated ELF dynamic table".into());
        }
        let mut tags = BTreeMap::new();
        let mut terminated = false;
        for row in bytes[range].chunks_exact(16) {
            let tag = elf_u64(row, 0)?;
            if tag == 0 {
                terminated = true;
                break;
            }
            // NEEDED, AUXILIARY, FILTER and POSFLAG_1 may occur more than once.
            if !matches!(tag, 1 | 0x7ffffffd | 0x7fffffff | 0x6ffffdfd)
                && tags.insert(tag, elf_u64(row, 8)?).is_some()
            {
                return Err("duplicate ELF dynamic tag".into());
            }
        }
        if !terminated {
            return Err("unterminated ELF dynamic table".into());
        }
        for (pointer, length, entry_tag, entry) in [
            (5, 10, None, 1),
            (7, 8, Some(9), 24),
            (17, 18, Some(19), 16),
            (36, 35, Some(37), 8),
            (25, 27, None, 8),
            (26, 28, None, 8),
            (32, 33, None, 8),
        ] {
            match (tags.get(&pointer), tags.get(&length)) {
                (None, None) => {}
                (Some(&address), Some(&size)) => {
                    if size % entry != 0
                        || entry_tag.is_some_and(|tag| tags.get(&tag) != Some(&entry))
                    {
                        return Err(if pointer == 32 {
                            "invalid preinit array size"
                        } else {
                            "invalid ELF dynamic table size"
                        }
                        .into());
                    }
                    if size != 0 {
                        mapped_range(loads.iter().copied(), address, size, bytes.len())?;
                    }
                }
                _ => return Err("incomplete ELF dynamic table metadata".into()),
            }
        }
        if let Some(&address) = tags.get(&23) {
            let size = *tags.get(&2).ok_or("missing PLT relocation size")?;
            let entry = match tags.get(&20) {
                Some(7) => 24,
                Some(17) => 16,
                _ => return Err("invalid PLT relocation format".into()),
            };
            if size % entry != 0 {
                return Err("invalid PLT relocation size".into());
            }
            if size != 0 {
                mapped_range(loads.iter().copied(), address, size, bytes.len())?;
            }
        }
    }
    Ok(())
}

fn parse_elf(bytes: &[u8]) -> Result<elf::Binary> {
    validate_elf_bytes(bytes)?;
    match lief::Binary::from(&mut Cursor::new(bytes)) {
        Some(lief::Binary::ELF(binary)) => Ok(binary),
        _ => Err("cannot parse ELF".into()),
    }
}

fn run(opts: Options) -> Result<String> {
    validate_paths(&opts)?;
    let input = Snapshot::read(&opts.input)?;
    let mut report = String::new();
    let binary = parse_elf(&input.bytes)?;
    check_elf(&binary)?;
    let index = AnalysisIndex::new(&binary)?;
    let (candidates, automatic, mut skipped) = select_candidates(&binary, &index, &opts)?;
    let seed = match opts.seed {
        Some(seed) => seed,
        None => random_seed()?,
    };
    let mut selected = Vec::new();
    for candidate in candidates {
        match analyze(&binary, &index, candidate.start, candidate.size).map_err(Error::eligibility)
        {
            Ok(function) => {
                let (vm, vm_reason) = if opts.no_vm {
                    (None, None)
                } else {
                    match vm::plan(&function, &binary).map_err(Error::eligibility) {
                        Ok(mut plan) => {
                            plan.choose_architecture(seed, function.start)?;
                            (Some(plan), None)
                        }
                        Err(Error::Unsupported(reason)) => (None, Some(reason)),
                        Err(error) => return Err(error),
                    }
                };
                let plan = strong_plan(&function);
                let external_table = function.tables.iter().any(|table| {
                    table.kind == TableKind::Absolute
                        && table
                            .targets
                            .iter()
                            .any(|&target| !in_range(target, function.start, function.end))
                }) || function.dispatches.iter().any(|dispatch| {
                    dispatch
                        .targets
                        .iter()
                        .any(|&target| !in_range(target, function.start, function.end))
                });
                let reason = if external_table {
                    Some("pointer table with external targets requires layout mode")
                } else {
                    plan.as_ref().err().copied()
                };
                let chosen = if let Some(vm) = vm {
                    Plan::Vm(vm)
                } else if reason.is_some() {
                    Plan::Layout
                } else {
                    Plan::Strong(plan.unwrap())
                };
                selected.push(Selected {
                    candidate,
                    function,
                    plan: chosen,
                    vm_reason,
                });
            }
            Err(Error::Unsupported(reason)) if automatic => skipped.push(Skipped {
                address: candidate.start,
                reason,
            }),
            Err(err) => return Err(err),
        }
    }
    loop {
        let incompatible = selected.iter().position(|source| {
            let mut targets = source
                .function
                .tables
                .iter()
                .filter(|table| table.kind == TableKind::Absolute)
                .flat_map(|table| table.targets.iter())
                .chain(
                    source
                        .function
                        .dispatches
                        .iter()
                        .flat_map(|dispatch| dispatch.targets.iter()),
                )
                .chain(source.function.fixed_targets.iter());
            targets.any(|&target| {
                selected.iter().any(|destination| {
                    destination.function.start != source.function.start
                        && in_range(target, destination.function.start, destination.function.end)
                        && !destination
                            .function
                            .entries
                            .iter()
                            .any(|entry| entry.label == target && entry.window.is_some())
                })
            })
        });
        let Some(at) = incompatible else { break };
        let address = selected[at].function.start;
        let reason = "pointer target in selected function lacks an original entry trampoline";
        if !automatic {
            return Err(format!("0x{address:x}: {reason}").into());
        }
        selected.remove(at);
        skipped.push(Skipped {
            address,
            reason: reason.into(),
        });
    }
    if opts.inspect {
        writeln!(report, "seed {seed}").map_err(|e| e.to_string())?;
        if !automatic && selected.len() == 1 {
            let item = &selected[0];
            writeln!(
                report,
                "eligible 0x{:x}..0x{:x}  {} blocks  {}{}",
                item.function.start,
                item.function.end,
                item.vm()
                    .map_or(item.function.blocks.len(), vm::VmPlan::block_count),
                item.mode().name(),
                item.vm().map_or_else(String::new, |plan| format!(
                    "{} interpreter={}",
                    plan.architecture.label(),
                    vm::interpreter_variant(seed, item.function.start)
                ))
            )
            .map_err(|e| e.to_string())?;
            for block in &item.function.blocks {
                if item.vm().is_some_and(|plan| !plan.has_block(block.old)) {
                    continue;
                }
                let len = if item.mode() == Mode::Vm {
                    18
                } else {
                    block.len
                        + usize::from(
                            item.mode() == Mode::Strong
                                && fragment_endbr(&item.function, block, item.scratch()),
                        ) * 4
                        + item.scratch().prefix_len()
                };
                writeln!(report, "0x{:x}  {:3} bytes", block.old, len)
                    .map_err(|e| e.to_string())?;
            }
            if let Some(reason) = &item.vm_reason {
                writeln!(
                    report,
                    "0x{:x}  vm unavailable  {reason}",
                    item.function.start
                )
                .map_err(|e| e.to_string())?;
            }
        } else {
            for item in &selected {
                writeln!(
                    report,
                    "0x{:x}  {:4} bytes  {:3} blocks  {}  {}{}",
                    item.function.start,
                    item.candidate.size,
                    item.vm()
                        .map_or(item.function.blocks.len(), vm::VmPlan::block_count),
                    item.mode().name(),
                    item.candidate
                        .names
                        .iter()
                        .next()
                        .map(String::as_str)
                        .unwrap_or(""),
                    item.vm().map_or_else(String::new, |plan| format!(
                        "{} interpreter={}",
                        plan.architecture.label(),
                        vm::interpreter_variant(seed, item.function.start)
                    ))
                )
                .map_err(|e| e.to_string())?;
                if let Some(reason) = &item.vm_reason {
                    writeln!(
                        report,
                        "0x{:x}  vm unavailable  {reason}",
                        item.function.start
                    )
                    .map_err(|e| e.to_string())?;
                }
            }
        }
        for item in &skipped {
            writeln!(report, "0x{:x}  skipped  {}", item.address, item.reason)
                .map_err(|e| e.to_string())?;
        }
        writeln!(
            report,
            "{} eligible, {} skipped",
            selected.len(),
            skipped.len()
        )
        .map_err(|e| e.to_string())?;
        return Ok(report);
    }
    if selected.is_empty() {
        return Err("no eligible functions".into());
    }
    for item in &skipped {
        eprintln!("0x{:x}: skipped: {}", item.address, item.reason);
    }
    for item in &selected {
        if let Some(reason) = &item.vm_reason {
            eprintln!(
                "0x{:x}: vm unavailable: {reason}; using {}",
                item.function.start,
                item.mode().name()
            );
        }
    }
    drop(binary);
    loop {
        match rewrite(
            &input,
            &index,
            &opts,
            &selected,
            seed,
            skipped.len(),
            &mut report,
        )? {
            RewriteOutcome::Complete => return Ok(report),
            RewriteOutcome::UnreachableSource(address) if automatic => {
                let at = selected
                    .iter()
                    .position(|item| item.function.start == address)
                    .ok_or_else(|| {
                        Error::Invariant("unreachable source has no selected function".into())
                    })?;
                selected.remove(at);
                if selected.is_empty() {
                    return Err("no eligible functions".into());
                }
                eprintln!("0x{address:x}: skipped: retained source out of range");
                skipped.push(Skipped {
                    address,
                    reason: "retained source out of range".into(),
                });
            }
            RewriteOutcome::UnreachableSource(address) => {
                return Err(format!("0x{address:x}: retained source out of range").into());
            }
            RewriteOutcome::UnaddressableTable(address) if automatic => {
                let at = selected
                    .iter()
                    .position(|item| item.function.start == address)
                    .ok_or_else(|| {
                        Error::Invariant("unaddressable table has no selected function".into())
                    })?;
                selected.remove(at);
                if selected.is_empty() {
                    return Err("no eligible functions".into());
                }
                eprintln!("0x{address:x}: skipped: cloned absolute table out of range");
                skipped.push(Skipped {
                    address,
                    reason: "cloned absolute table out of range".into(),
                });
            }
            RewriteOutcome::UnaddressableTable(address) => {
                return Err(format!("0x{address:x}: cloned absolute table out of range").into());
            }
            RewriteOutcome::VmUnrepresentable(address, reason) => {
                let item = selected
                    .iter_mut()
                    .find(|item| item.function.start == address && item.mode() == Mode::Vm)
                    .ok_or_else(|| {
                        Error::Invariant("VM fallback has no selected function".into())
                    })?;
                item.vm_reason = Some(reason.clone());
                item.plan = match strong_plan(&item.function) {
                    Ok(scratch) => Plan::Strong(scratch),
                    Err(_) => Plan::Layout,
                };
                eprintln!(
                    "0x{address:x}: vm unavailable: {reason}; using {}",
                    item.mode().name()
                );
            }
        }
    }
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Self::Vm => "vm",
            Self::Strong => "strong",
            Self::Layout => "layout",
        }
    }
}

fn random_seed() -> Result<u64> {
    let mut bytes = [0; 8];
    fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|e| format!("cannot read /dev/urandom: {e}"))?;
    Ok(u64::from_le_bytes(bytes))
}

fn check_elf(binary: &elf::Binary) -> Result<()> {
    let hdr = binary.header();
    if hdr.identity_class() != header::Class::ELF64
        || hdr.identity_data() != header::ElfData::LSB
        || hdr.machine_type() != header::Arch::X86_64
        || !matches!(
            hdr.file_type(),
            header::FileType::EXEC | header::FileType::DYN
        )
        || binary.interpreter().is_empty()
    {
        return Err("requires a dynamic Linux x86-64 executable (ET_EXEC or PIE)".into());
    }
    Ok(())
}

fn select_candidates(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    opts: &Options,
) -> Result<(Vec<Candidate>, bool, Vec<Skipped>)> {
    if let Some(address) = opts.address {
        return Ok((
            vec![Candidate {
                start: address,
                size: opts.size.unwrap(),
                names: BTreeSet::new(),
            }],
            false,
            Vec::new(),
        ));
    }
    let mut by_address: BTreeMap<u64, BTreeMap<u64, BTreeSet<String>>> = BTreeMap::new();
    let mut all_names = BTreeSet::new();
    for sym in binary.symtab_symbols().chain(binary.dynamic_symbols()) {
        if sym.get_type() == symbol::Type::FUNC && sym.size() != 0 && sym.value() != 0 {
            let name = sym.name();
            all_names.insert(name.clone());
            by_address
                .entry(sym.value())
                .or_default()
                .entry(sym.size())
                .or_default()
                .insert(name);
        }
    }
    if opts.symbols.is_empty() {
        for frame in &index.fdes {
            if frame.end <= frame.start {
                continue;
            }
            let size = frame.end - frame.start;
            if by_address.contains_key(&frame.start)
                || by_address.iter().any(|(&start, sizes)| {
                    sizes
                        .keys()
                        .any(|&len| start < frame.end && start.saturating_add(len) > frame.start)
                })
            {
                continue;
            }
            by_address
                .entry(frame.start)
                .or_default()
                .entry(size)
                .or_default();
        }
    }
    for name in &opts.exclude {
        if !all_names.contains(name) {
            return Err(format!("unknown sized function: {name}").into());
        }
    }
    let automatic = opts.symbols.is_empty();
    let mut skipped = Vec::new();
    let mut candidates = Vec::new();
    for (start, sizes) in by_address {
        if sizes.len() != 1 {
            if automatic {
                skipped.push(Skipped {
                    address: start,
                    reason: "ambiguous function size".into(),
                });
            }
            continue;
        }
        let (size, names) = sizes.into_iter().next().unwrap();
        if automatic && !names.is_disjoint(&opts.exclude) {
            continue;
        }
        candidates.push(Candidate { start, size, names });
    }
    if !automatic {
        let mut picked = BTreeMap::new();
        for name in &opts.symbols {
            let matches: Vec<_> = candidates
                .iter()
                .filter(|c| c.names.contains(name))
                .collect();
            if matches.len() != 1 {
                return Err(format!(
                    "expected one sized function named {name}, found {}",
                    matches.len()
                )
                .into());
            }
            let candidate = matches[0];
            picked.insert(candidate.start, (candidate.size, candidate.names.clone()));
        }
        candidates = picked
            .into_iter()
            .map(|(start, (size, names))| Candidate { start, size, names })
            .collect();
    }
    Ok((candidates, automatic, skipped))
}

fn in_range(va: u64, start: u64, end: u64) -> bool {
    va >= start && va < end
}

fn internal_edges(function: &Function) -> Vec<(u64, usize, u64)> {
    let mut edges = Vec::new();
    for block in &function.blocks {
        let targets = match block.exit {
            Exit::Branch {
                target,
                fallthrough,
                ..
            } => [Some(target), Some(fallthrough)],
            Exit::Jump(target) | Exit::Fallthrough(target) => [Some(target), None],
            Exit::Return | Exit::Table(_) | Exit::Dispatch(_) => [None, None],
        };
        for (arm, target) in targets.into_iter().enumerate() {
            if let Some(target) = target
                && in_range(target, function.start, function.end)
            {
                edges.push((block.old, arm, target));
            }
        }
        if let Exit::Table(index) = block.exit {
            edges.extend(
                function.tables[index]
                    .internal_unique(function)
                    .into_iter()
                    .enumerate()
                    .map(|(arm, target)| (block.old, arm, target)),
            );
        }
        if let Exit::Dispatch(index) = block.exit {
            edges.extend(
                function.dispatches[index]
                    .targets
                    .iter()
                    .copied()
                    .filter(|&target| in_range(target, function.start, function.end))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .enumerate()
                    .map(|(arm, target)| (block.old, arm, target)),
            );
        }
    }
    edges
}

fn xmm_index(register: Register) -> Option<u8> {
    let value = register as u32;
    for base in [Register::XMM0, Register::YMM0, Register::ZMM0] {
        let first = base as u32;
        if (first..first + 16).contains(&value) {
            return Some((value - first) as u8);
        }
    }
    None
}

fn whole_simd_state(mnemonic: Mnemonic) -> bool {
    matches!(
        mnemonic,
        Mnemonic::Vzeroall
            | Mnemonic::Fxsave
            | Mnemonic::Fxsave64
            | Mnemonic::Fxrstor
            | Mnemonic::Fxrstor64
            | Mnemonic::Xsave
            | Mnemonic::Xsave64
            | Mnemonic::Xsaveopt
            | Mnemonic::Xsaveopt64
            | Mnemonic::Xsavec
            | Mnemonic::Xsavec64
            | Mnemonic::Xsaves
            | Mnemonic::Xsaves64
            | Mnemonic::Xrstor
            | Mnemonic::Xrstor64
            | Mnemonic::Xrstors
            | Mnemonic::Xrstors64
    )
}

fn strong_plan(function: &Function) -> std::result::Result<Scratch, &'static str> {
    if function.blocks.iter().any(|block| {
        matches!(block.exit, Exit::Fallthrough(target) if target == function.end)
            && block.body.last().is_some_and(|last| {
                !matches!(
                    last.flow_control(),
                    FlowControl::Call | FlowControl::IndirectCall
                )
            })
    }) {
        return Err("terminal fallthrough requires layout mode");
    }
    if internal_edges(function).is_empty() && !function.blocks.iter().any(|b| b.body.len() >= 4) {
        return Err("too short for fragment routing");
    }
    let mut info = InstructionInfoFactory::new();
    let mut decoder = Decoder::with_ip(64, &function.bytes, function.start, DecoderOptions::NONE);
    let mut occupied = [false; 16];
    let mut state_instruction = false;
    let mut internal_call = false;
    while decoder.can_decode() {
        let instr = decoder.decode();
        state_instruction |= whole_simd_state(instr.mnemonic());
        internal_call |= instr.flow_control() == FlowControl::Call
            && instr.is_call_near()
            && instr.near_branch_target() != function.start
            && in_range(instr.near_branch_target(), function.start, function.end);
        for used in info.info(&instr).used_registers() {
            if let Some(index) = xmm_index(used.register()) {
                occupied[index as usize] = true;
            }
        }
    }
    if state_instruction {
        return Err("SIMD state instruction requires layout mode");
    }
    if internal_call {
        return Err("internal call enters function interior");
    }
    let mut free = (8..16).filter(|&index| !occupied[index as usize]);
    let mut scratch = Scratch {
        r10: free.next(),
        r11: free.next(),
        state: free.next(),
        rcx: None,
    };
    if scratch.r10.is_none() || scratch.r11.is_none() || scratch.state.is_none() {
        return Err("no spare XMM registers for strong routing");
    }
    if let Some(rows) = &function.unwind {
        let affected = |register: u16| {
            register == 10
                || register == 11
                || [scratch.r10, scratch.r11, scratch.state]
                    .into_iter()
                    .flatten()
                    .any(|index| register == index as u16 + 17)
        };
        if rows.iter().any(|(_, row)| {
            affected(row.cfa_register)
                || row.registers.iter().any(|(&register, rule)| {
                    affected(register)
                        || matches!(rule, FrameRegisterRule::Register(other) if affected(*other))
                })
        }) {
            return Err("unwind rule uses route scratch");
        }
    }
    scratch.rcx = free.find(|&slot| {
        function.unwind.as_ref().is_none_or(|rows| {
            let affected = |register: u16| register == 2 || register == slot as u16 + 17;
            !rows.iter().any(|(_, row)| {
                affected(row.cfa_register) || row.registers.iter().any(|(&register, rule)| {
                    affected(register)
                        || matches!(rule, FrameRegisterRule::Register(other) if affected(*other))
                })
            })
        })
    });
    Ok(scratch)
}

fn split_fragments(function: &Function, seed: u64, scratch: Scratch) -> Vec<Block> {
    let mut parts = Vec::new();
    for block in &function.blocks {
        let mut cursor = 0;
        let mut state = function_seed(seed, block.old);
        while cursor < block.body.len() {
            let remaining = block.body.len() - cursor;
            let count = if cursor == 0 && (4..=5).contains(&remaining) {
                2
            } else if remaining <= 5 {
                remaining
            } else {
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                (2 + (state.wrapping_mul(0x2545f4914f6cdd1d) % 4) as usize).min(remaining - 2)
            };
            let stop = cursor + count;
            let exit = if stop == block.body.len() {
                block.exit
            } else {
                Exit::Fallthrough(block.body[stop].ip())
            };
            let tail = match exit {
                Exit::Branch {
                    target,
                    fallthrough,
                    ..
                } if in_range(target, function.start, function.end)
                    && in_range(fallthrough, function.start, function.end) =>
                {
                    PAIRED_BRANCH_TAIL_LEN + scratch.route_len()
                }
                Exit::Branch { .. } => 11,
                Exit::Jump(_) | Exit::Fallthrough(_) | Exit::Dispatch(_) => 5,
                Exit::Return => 0,
                Exit::Table(index) => usize::from(function.tables[index].setup.is_some()) * 7,
            };
            parts.push(Block {
                old: block.body[cursor].ip(),
                body: block.body[cursor..stop].to_vec(),
                exit,
                len: block.body[cursor..stop]
                    .iter()
                    .map(|ins| ins.len())
                    .sum::<usize>()
                    + block.body[cursor..stop]
                        .iter()
                        .filter(|ins| {
                            matches!(
                                ins.flow_control(),
                                FlowControl::Call | FlowControl::IndirectCall
                            )
                        })
                        .count()
                        * scratch.reset_len()
                    + block.body[cursor..stop]
                        .iter()
                        .filter(|ins| {
                            function.tables.iter().any(|table| {
                                table.setup.is_some_and(|setup| setup.load == ins.ip())
                            })
                        })
                        .count()
                        * 7
                    + tail,
            });
            cursor = stop;
        }
        if block.body.is_empty() {
            let tail = match block.exit {
                Exit::Branch {
                    target,
                    fallthrough,
                    ..
                } if in_range(target, function.start, function.end)
                    && in_range(fallthrough, function.start, function.end) =>
                {
                    PAIRED_BRANCH_TAIL_LEN + scratch.route_len()
                }
                _ => block.len,
            };
            parts.push(Block {
                old: block.old,
                body: Vec::new(),
                exit: block.exit,
                len: tail,
            });
        }
    }
    parts
}

fn alternate_target(function: &Function, block: &Block, starts: &[u64], seed: u64) -> Option<u64> {
    let real: Vec<u64> = match block.exit {
        Exit::Branch {
            target,
            fallthrough,
            ..
        } => vec![target, fallthrough],
        Exit::Jump(target) | Exit::Fallthrough(target) => vec![target],
        Exit::Table(index) => function.tables[index].targets.clone(),
        Exit::Dispatch(index) => function.dispatches[index].targets.clone(),
        Exit::Return => return None,
    };
    if !real
        .iter()
        .any(|&target| in_range(target, function.start, function.end))
    {
        return None;
    }
    let candidates: Vec<_> = starts
        .iter()
        .copied()
        .filter(|&target| target != block.old && !real.contains(&target))
        .collect();
    (!candidates.is_empty()).then(|| {
        let pick = function_seed(seed ^ 0x5be0cd19137e2179, block.old) as usize % candidates.len();
        candidates[pick]
    })
}

struct AnalysisIndex {
    fdes: Vec<FrameRange>,
    functions: Vec<(u64, u64)>,
    relocation_sites: BTreeSet<u64>,
    relocation_targets: BTreeSet<u64>,
    relocation_target_sites: BTreeMap<u64, BTreeSet<u64>>,
    relative_slots: BTreeMap<u64, Option<u64>>,
    references: BTreeMap<u64, Vec<IncomingReference>>,
}

struct IncomingReference {
    source: u64,
    direct: bool,
    offset: Option<usize>,
    next: u64,
}

fn eh_bases(binary: &elf::Binary) -> BaseAddresses {
    let mut bases = BaseAddresses::default();
    for (name, kind) in [
        (".eh_frame", 0),
        (".eh_frame_hdr", 1),
        (".text", 2),
        (".got", 3),
    ] {
        if let Some(section) = binary.section_by_name(name) {
            bases = match kind {
                0 => bases.set_eh_frame(section.virtual_address()),
                1 => bases.set_eh_frame_hdr(section.virtual_address()),
                2 => bases.set_text(section.virtual_address()),
                _ => bases.set_got(section.virtual_address()),
            };
        }
    }
    bases
}

impl AnalysisIndex {
    fn new(binary: &elf::Binary) -> Result<Self> {
        let mut fdes = Vec::new();
        if let Some(sec) = binary.section_by_name(".eh_frame") {
            let frame = EhFrame::new(sec.content(), LittleEndian);
            let bases = eh_bases(binary);
            let mut entries = frame.entries(&bases);
            while let Some(entry) = entries
                .next()
                .map_err(|e| format!("cannot read .eh_frame: {e}"))?
            {
                if let CieOrFde::Fde(partial) = entry {
                    let fde = partial
                        .parse(|section, bases, offset| section.cie_from_offset(bases, offset))
                        .map_err(|e| format!("cannot read .eh_frame FDE: {e}"))?;
                    fdes.push(FrameRange {
                        start: fde.initial_address(),
                        end: fde.end_address(),
                        offset: fde.offset(),
                        unsupported: fde.lsda().is_some()
                            || fde.personality().is_some()
                            || fde.is_signal_trampoline(),
                    });
                }
            }
        } else if binary
            .segments()
            .any(|s| s.p_type() == segment::Type::GNU_EH_FRAME)
        {
            return Err("unwind header present without a readable .eh_frame section".into());
        }

        let functions = binary
            .symtab_symbols()
            .chain(binary.dynamic_symbols())
            .filter(|s| s.get_type() == symbol::Type::FUNC)
            .map(|s| (s.value(), s.value().saturating_add(s.size())))
            .collect();
        let mut relocation_sites = BTreeSet::new();
        let mut relocation_targets = BTreeSet::new();
        let mut relocation_target_sites: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
        let mut relative_slots = BTreeMap::new();
        for rel in binary.relocations() {
            relocation_sites.insert(rel.address());
            let relative = (rel.get_type() == relocation::Type::X86_64_RELATIVE
                && rel.purpose() == relocation::Purpose::DYNAMIC
                && rel.is_rela()
                && rel.addend() >= 0
                && rel
                    .symbol()
                    .is_none_or(|symbol| symbol.name().is_empty() && symbol.value() == 0))
            .then_some(rel.addend() as u64);
            match relative_slots.entry(rel.address()) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(relative);
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    entry.insert(None);
                }
            }
            let addend = rel.addend();
            if addend > 0 {
                relocation_targets.insert(addend as u64);
                relocation_target_sites
                    .entry(addend as u64)
                    .or_default()
                    .insert(rel.address());
            }
            if let Some(sym) = rel.symbol() {
                let target = sym.value() as i128 + addend as i128;
                if let Ok(target) = u64::try_from(target) {
                    relocation_targets.insert(target);
                    relocation_target_sites
                        .entry(target)
                        .or_default()
                        .insert(rel.address());
                }
            }
        }
        let mut references: BTreeMap<u64, Vec<IncomingReference>> = BTreeMap::new();
        let mut saw_exec = false;
        for sec in binary.sections() {
            if !sec.flags().contains(section::Flags::EXECINSTR) || sec.content().is_empty() {
                continue;
            }
            saw_exec = true;
            let mut decoder = Decoder::with_ip(
                64,
                sec.content(),
                sec.virtual_address(),
                DecoderOptions::NONE,
            );
            while decoder.can_decode() {
                let instr = decoder.decode();
                let target = match instr.flow_control() {
                    FlowControl::Call if instr.is_call_near() => Some(instr.near_branch_target()),
                    FlowControl::UnconditionalBranch if instr.is_jmp_short_or_near() => {
                        Some(instr.near_branch_target())
                    }
                    FlowControl::ConditionalBranch if instr.is_jcc_short_or_near() => {
                        Some(instr.near_branch_target())
                    }
                    _ => None,
                };
                if let Some(target) = target {
                    let offsets = decoder.get_constant_offsets(&instr);
                    let offset =
                        (offsets.immediate_size() == 4).then_some(offsets.immediate_offset());
                    references
                        .entry(target)
                        .or_default()
                        .push(IncomingReference {
                            source: instr.ip(),
                            direct: true,
                            offset,
                            next: instr.next_ip(),
                        });
                }
                if instr.is_ip_rel_memory_operand() {
                    references
                        .entry(instr.ip_rel_memory_address())
                        .or_default()
                        .push(IncomingReference {
                            source: instr.ip(),
                            direct: false,
                            offset: None,
                            next: instr.next_ip(),
                        });
                } else if instr.memory_base() == Register::None
                    && instr.memory_displ_size() != 0
                    && (0..instr.op_count()).any(|operand| instr.op_kind(operand) == OpKind::Memory)
                {
                    references
                        .entry(instr.memory_displacement64())
                        .or_default()
                        .push(IncomingReference {
                            source: instr.ip(),
                            direct: false,
                            offset: None,
                            next: instr.next_ip(),
                        });
                }
            }
        }
        if !saw_exec {
            return Err("executable sections are required for incoming-reference checks".into());
        }
        Ok(Self {
            fdes,
            functions,
            relocation_sites,
            relocation_targets,
            relocation_target_sites,
            relative_slots,
            references,
        })
    }

    fn check(
        &self,
        start: u64,
        end: u64,
        allowed_relocation_sites: &BTreeSet<u64>,
    ) -> Result<Vec<u64>> {
        for &(lo, hi) in &self.functions {
            if (lo > start && lo < end) || (lo < start && hi > start) {
                return Err(format!("function symbol overlaps selected range at 0x{lo:x}").into());
            }
        }
        if let Some(site) = self.relocation_sites.range(start..end).next() {
            return Err(format!("relocation inside selected function at 0x{site:x}").into());
        }
        if let Some(target) = self
            .relocation_targets
            .range(start + 1..end)
            .find(|target| {
                self.relocation_target_sites
                    .get(target)
                    .is_none_or(|sites| {
                        !sites
                            .iter()
                            .all(|site| allowed_relocation_sites.contains(site))
                    })
            })
        {
            return Err(format!("relocation points into function interior at 0x{target:x}").into());
        }
        let mut entries = vec![start];
        for (&target, sources) in self.references.range(start + 1..end) {
            if sources.iter().all(|site| in_range(site.source, start, end)) {
                continue;
            }
            if sources
                .iter()
                .any(|site| !in_range(site.source, start, end) && !site.direct)
            {
                return Err(
                    format!("data reference enters function interior at 0x{target:x}").into(),
                );
            }
            entries.push(target);
        }
        Ok(entries)
    }

    fn unwind_for(
        &self,
        binary: &elf::Binary,
        start: u64,
        end: u64,
    ) -> Result<Option<Vec<(u64, UnwindRule)>>> {
        let matches: Vec<_> = self
            .fdes
            .iter()
            .filter(|fde| fde.start < end && fde.end > start)
            .collect();
        if matches.is_empty() {
            return Ok(None);
        }
        if matches.len() != 1 || matches[0].start > start || matches[0].end < end {
            return Err("ambiguous or partial unwind FDE".into());
        }
        let matched = matches[0];
        if matched.unsupported {
            return Err("unwind FDE has an LSDA or personality".into());
        }
        if !binary
            .segments()
            .any(|seg| seg.p_type() == segment::Type::GNU_EH_FRAME)
        {
            return Err("unwind FDE requires PT_GNU_EH_FRAME".into());
        }
        let section = binary
            .section_by_name(".eh_frame")
            .ok_or("missing .eh_frame")?;
        let frame = EhFrame::new(section.content(), LittleEndian);
        let bases = eh_bases(binary);
        let fde = frame
            .fde_from_offset(
                &bases,
                EhFrameOffset(matched.offset),
                |section, bases, offset| section.cie_from_offset(bases, offset),
            )
            .map_err(|e| format!("cannot read unwind FDE: {e}"))?;
        let mut context = UnwindContext::new();
        let mut table = fde
            .rows(&frame, &bases, &mut context)
            .map_err(|e| format!("cannot read unwind rows: {e}"))?;
        let mut rows = Vec::new();
        while let Some(row) = table
            .next_row()
            .map_err(|e| format!("cannot read unwind row: {e}"))?
        {
            if row.end_address() <= start || row.start_address() >= end {
                continue;
            }
            if row.saved_args_size() != 0 {
                return Err("unwind arguments size is unsupported".into());
            }
            let (register, offset) = match row.cfa() {
                CfaRule::RegisterAndOffset { register, offset } => (register.0, *offset),
                CfaRule::Expression(_) => return Err("unwind CFA expression is unsupported".into()),
            };
            let mut registers = BTreeMap::new();
            for &(register, ref rule) in row.registers() {
                let converted = match rule {
                    RegisterRule::Undefined => FrameRegisterRule::Undefined,
                    RegisterRule::SameValue => FrameRegisterRule::SameValue,
                    RegisterRule::Offset(value) => FrameRegisterRule::Offset(
                        i32::try_from(*value).map_err(|_| "unwind offset out of range")?,
                    ),
                    RegisterRule::ValOffset(value) => FrameRegisterRule::ValOffset(
                        i32::try_from(*value).map_err(|_| "unwind offset out of range")?,
                    ),
                    RegisterRule::Register(value) => FrameRegisterRule::Register(value.0),
                    _ => return Err("unwind register expression is unsupported".into()),
                };
                registers.insert(register.0, converted);
            }
            rows.push((
                row.start_address().max(start),
                UnwindRule {
                    cfa_register: register,
                    cfa_offset: i32::try_from(offset)
                        .map_err(|_| "unwind CFA offset out of range")?,
                    cfa_expression: None,
                    registers,
                },
            ));
        }
        if rows.first().is_none_or(|row| row.0 != start) {
            return Err("unwind FDE has no row at function entry".into());
        }
        Ok(Some(rows))
    }
}

fn relative_dispatch(load: &Instruction, add: &Instruction, jump: &Instruction) -> bool {
    load.mnemonic() == Mnemonic::Movsxd
        && load.op0_kind() == OpKind::Register
        && load.op0_register().size() == 8
        && load.op1_kind() == OpKind::Memory
        && load.memory_base().size() == 8
        && load.memory_index().size() == 8
        && load.memory_index_scale() == 4
        && load.memory_displacement64() == 0
        && load.segment_prefix() == Register::None
        && add.mnemonic() == Mnemonic::Add
        && add.op0_kind() == OpKind::Register
        && add.op1_kind() == OpKind::Register
        && add.op0_register() == load.op0_register()
        && add.op1_register() == load.memory_base()
        && jump.flow_control() == FlowControl::IndirectBranch
        && jump.op0_kind() == OpKind::Register
        && jump.op0_register() == load.op0_register()
        && load.memory_base() != load.memory_index()
        && load.memory_base() != load.op0_register()
}

fn jump_table_local(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<JumpTable> {
    let jump = instructions[at];
    let unsupported =
        || Error::Unsupported(format!("unsupported indirect jump at 0x{:x}", jump.ip()));
    if at < 5 || jump.op0_kind() != OpKind::Register {
        return Err(unsupported());
    }
    let add = instructions[at - 1];
    let load = instructions[at - 2];
    if !relative_dispatch(&load, &add, &jump) {
        return Err(unsupported());
    }
    let index_reg = load.memory_index();
    let (lea_at, source_reg) = if instructions[at - 3].mnemonic() == Mnemonic::Movzx {
        let zero = instructions[at - 3];
        if at < 6
            || zero.op0_kind() != OpKind::Register
            || zero.op1_kind() != OpKind::Register
            || !matches!(zero.op0_register().size(), 4 | 8)
            || zero.op0_register().full_register() != index_reg
        {
            return Err(unsupported());
        }
        (at - 4, zero.op1_register())
    } else {
        (at - 3, load.memory_index())
    };
    let lea = instructions[lea_at];
    let guard = instructions[lea_at - 1];
    let cmp = instructions[lea_at - 2];
    if lea.mnemonic() != Mnemonic::Lea
        || lea.op0_kind() != OpKind::Register
        || !lea.is_ip_rel_memory_operand()
        || lea.op0_register() != add.op1_register()
        || source_reg.full_register() == add.op1_register().full_register()
        || !guard.is_jcc_short_or_near()
        || guard.condition_code() != ConditionCode::a
        || guard.next_ip() != lea.ip()
        || cmp.mnemonic() != Mnemonic::Cmp
        || cmp.op0_kind() != OpKind::Register
        || cmp.op0_register() != source_reg
    {
        return Err(unsupported());
    }
    let bound = match cmp.op1_kind() {
        OpKind::Immediate8 => cmp.immediate8() as u64,
        OpKind::Immediate8to32 => cmp.immediate8to32() as u64,
        OpKind::Immediate32 => cmp.immediate32() as u64,
        _ => return Err(unsupported()),
    };
    if bound >= 256
        || index
            .references
            .range(guard.ip()..=jump.ip())
            .next()
            .is_some()
    {
        return Err(unsupported());
    }
    let base = lea.ip_rel_memory_address();
    let targets = relative_table_entries(
        binary,
        index,
        ips,
        base,
        bound + 1,
        TableSite { start, end },
    )
    .ok_or_else(unsupported)?;
    if targets
        .iter()
        .any(|&target| in_range(target, guard.ip(), jump.next_ip()))
    {
        return Err(unsupported());
    }
    Ok(JumpTable {
        lea: lea.ip(),
        jump: jump.ip(),
        guard: guard.ip(),
        targets,
        setup: None,
        kind: TableKind::Relative,
        original_base: base,
    })
}

fn jump_table(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<JumpTable> {
    jump_table_local(binary, index, instructions, at, ips, start, end)
        .or_else(|_| jump_table_traced(binary, index, instructions, at, ips, start, end))
        .or_else(|_| jump_table_absolute(binary, index, instructions, at, ips, start, end))
}

fn writes_register(
    info: &mut InstructionInfoFactory,
    instruction: &Instruction,
    register: Register,
) -> bool {
    for used in info.info(instruction).used_registers() {
        if used.register().full_register() == register
            && matches!(
                used.access(),
                OpAccess::Write
                    | OpAccess::CondWrite
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite
            )
        {
            return true;
        }
    }
    false
}

fn zero_extended_before(
    index: &AnalysisIndex,
    instructions: &[Instruction],
    cmp_at: usize,
    register: Register,
    info: &mut InstructionInfoFactory,
) -> bool {
    for at in (0..cmp_at).rev().take(32) {
        let instruction = &instructions[at];
        if instruction.flow_control() != FlowControl::Next {
            return false;
        }
        if !writes_register(info, instruction, register) {
            continue;
        }
        if instruction.op0_kind() != OpKind::Register
            || instruction.op0_register().full_register() != register
            || instruction.op0_register().size() != 4
            || !info.info(instruction).used_registers().iter().any(|used| {
                used.register().full_register() == register
                    && matches!(used.access(), OpAccess::Write | OpAccess::ReadWrite)
            })
        {
            return false;
        }
        return index
            .references
            .range(instruction.next_ip()..=instructions[cmp_at].ip())
            .next()
            .is_none();
    }
    false
}

struct IndexGuard {
    bound: u64,
    branch: u64,
}

fn guarded_index(
    index: &AnalysisIndex,
    instructions: &[Instruction],
    load_at: usize,
    jump_at: usize,
    index_reg: Register,
) -> Option<IndexGuard> {
    if load_at < 2 {
        return None;
    }
    let jump = instructions[jump_at];
    let mut info = InstructionInfoFactory::new();
    for cmp_at in (0..load_at - 1).rev().take(32) {
        let cmp = instructions[cmp_at];
        let guard = instructions[cmp_at + 1];
        if cmp.mnemonic() != Mnemonic::Cmp
            || cmp.op0_kind() != OpKind::Register
            || !guard.is_jcc_short_or_near()
            || guard.condition_code() != ConditionCode::a
            || cmp.next_ip() != guard.ip()
            || in_range(guard.near_branch_target(), guard.ip(), jump.next_ip())
            || index
                .references
                .range(guard.ip()..=jump.ip())
                .next()
                .is_some()
        {
            continue;
        }
        let bound = match cmp.op1_kind() {
            OpKind::Immediate8 => cmp.immediate8() as u64,
            OpKind::Immediate8to32 => cmp.immediate8to32() as u64,
            OpKind::Immediate8to64 => cmp.immediate8to64() as u64,
            OpKind::Immediate32 => cmp.immediate32() as u64,
            OpKind::Immediate32to64 => cmp.immediate32to64() as u64,
            _ => continue,
        };
        if bound >= 1024 {
            continue;
        }
        let source = cmp.op0_register();
        let same_index = source.full_register() == index_reg && source.size() >= 4;
        let mut bounded = same_index
            && (source.size() == 8
                || (source.size() == 4
                    && zero_extended_before(index, instructions, cmp_at, index_reg, &mut info)));
        let mut valid = true;
        for instruction in &instructions[cmp_at + 2..load_at] {
            if instruction.flow_control() != FlowControl::Next {
                valid = false;
                break;
            }
            if !bounded
                && instruction.mnemonic() == Mnemonic::Movzx
                && instruction.op0_kind() == OpKind::Register
                && instruction.op1_kind() == OpKind::Register
                && instruction.op0_register().full_register() == index_reg
                && instruction.op0_register().size() >= 4
                && instruction.op1_register() == source
            {
                bounded = true;
                continue;
            }
            let copy = instruction.mnemonic() == Mnemonic::Mov
                && instruction.op0_kind() == OpKind::Register
                && instruction.op1_kind() == OpKind::Register
                && instruction.op0_register().full_register() == index_reg
                && instruction.op0_register().size() == 4
                && instruction.op1_register() == source
                && source.size() == 4;
            if copy && !bounded {
                bounded = true;
                continue;
            }
            let writes_index = writes_register(&mut info, instruction, index_reg);
            let writes_source = writes_register(&mut info, instruction, source.full_register());
            if writes_index || (writes_source && !bounded) {
                valid = false;
                break;
            }
        }
        if valid && bounded {
            return Some(IndexGuard {
                bound,
                branch: guard.ip(),
            });
        }
    }
    None
}

struct TableSite {
    start: u64,
    end: u64,
}

fn relative_table_entries(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    ips: &BTreeSet<u64>,
    base: u64,
    count: u64,
    site: TableSite,
) -> Option<Vec<u64>> {
    let byte_len = count.checked_mul(4)?;
    let table_end = base.checked_add(byte_len)?;
    if !binary.segments().any(|seg| {
        seg.p_type() == segment::Type::LOAD
            && seg.flags() & segment::Flags::R.bits() != 0
            && seg.flags() & (segment::Flags::W | segment::Flags::X).bits() == 0
            && base >= seg.virtual_address()
            && seg
                .virtual_address()
                .checked_add(seg.physical_size())
                .is_some_and(|end| table_end <= end)
    }) || index
        .relocation_sites
        .range(base.saturating_sub(7)..table_end)
        .next()
        .is_some()
        || index
            .relocation_targets
            .range(base..table_end)
            .next()
            .is_some()
        || index.references.range(base..table_end).any(|(_, sources)| {
            sources
                .iter()
                .any(|reference| !in_range(reference.source, site.start, site.end))
        })
    {
        return None;
    }
    let content = binary.content_from_virtual_address(base, byte_len);
    if content.len() != usize::try_from(byte_len).ok()? {
        return None;
    }
    let mut targets = Vec::with_capacity(usize::try_from(count).ok()?);
    for word in content.chunks_exact(4) {
        let offset = i32::from_le_bytes(word.try_into().ok()?);
        let target = u64::try_from(base as i128 + offset as i128).ok()?;
        if !in_range(target, site.start, site.end) || !ips.contains(&target) {
            return None;
        }
        targets.push(target);
    }
    Some(targets)
}

fn relative_table_candidates(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<Vec<JumpTable>> {
    let unsupported = || {
        Error::Unsupported(format!(
            "unsupported indirect jump at 0x{:x}",
            instructions[at].ip()
        ))
    };
    if at < 3 {
        return Err(unsupported());
    }
    let jump = instructions[at];
    let add = instructions[at - 1];
    let load = instructions[at - 2];
    if !relative_dispatch(&load, &add, &jump) {
        return Err(unsupported());
    }
    let base_reg = load.memory_base();
    let index_reg = load.memory_index();
    let guard =
        guarded_index(index, instructions, at - 2, at, index_reg).ok_or_else(unsupported)?;
    let mut candidates = Vec::new();
    for lea in instructions.iter().rev() {
        if lea.mnemonic() != Mnemonic::Lea
            || lea.op0_kind() != OpKind::Register
            || lea.op0_register() != base_reg
            || !lea.is_ip_rel_memory_operand()
        {
            continue;
        }
        let base = lea.ip_rel_memory_address();
        let Some(targets) = relative_table_entries(
            binary,
            index,
            ips,
            base,
            guard.bound + 1,
            TableSite { start, end },
        ) else {
            continue;
        };
        if targets.iter().copied().collect::<BTreeSet<_>>().len() > 128
            || targets
                .iter()
                .any(|&target| in_range(target, guard.branch, jump.next_ip()))
        {
            continue;
        }
        let table = JumpTable {
            lea: lea.ip(),
            jump: jump.ip(),
            guard: guard.branch,
            targets,
            setup: Some(TableSetup {
                load: load.ip(),
                register: base_reg,
                original: base,
            }),
            kind: TableKind::Relative,
            original_base: base,
        };
        candidates.push(table);
    }
    Ok(candidates)
}

fn jump_table_traced(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<JumpTable> {
    if instructions
        .iter()
        .filter(|i| i.flow_control() == FlowControl::IndirectBranch)
        .count()
        == 1
    {
        let candidates =
            relative_table_candidates(binary, index, instructions, at, ips, start, end)?;
        if let Some(first) = candidates.first() {
            let entries = table_entries(index, instructions, start, end)?;
            let indirect = BTreeMap::from([(
                instructions[at].ip(),
                candidates
                    .iter()
                    .flat_map(|table| table.targets.iter().copied())
                    .collect(),
            )]);
            let edges = table_successors(instructions, &indirect)?;
            let known = table_base_states(
                instructions,
                &edges,
                &entries,
                first.setup.as_ref().unwrap().register,
            );
            for table in candidates {
                if table.lea < instructions[at - 2].ip()
                    && [at - 2, at - 1, at]
                        .iter()
                        .all(|&site| known[site] == Some(table.original_base))
                {
                    return Ok(table);
                }
            }
        }
    }
    Err(Error::Unsupported(format!(
        "unsupported indirect jump at 0x{:x}",
        instructions[at].ip()
    )))
}

fn table_entries(
    index: &AnalysisIndex,
    instructions: &[Instruction],
    start: u64,
    end: u64,
) -> Result<Vec<usize>> {
    let addresses: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(at, i)| (i.ip(), at))
        .collect();
    let mut entries: Vec<_> = index
        .check(start, end, &BTreeSet::new())?
        .into_iter()
        .map(|ip| {
            addresses
                .get(&ip)
                .copied()
                .ok_or("entry is not an instruction boundary")
        })
        .collect::<std::result::Result<_, _>>()?;
    for instruction in instructions {
        if instruction.is_call_near() && in_range(instruction.near_branch_target(), start, end) {
            entries.push(
                *addresses
                    .get(&instruction.near_branch_target())
                    .ok_or("call enters an instruction")?,
            );
        }
    }
    entries.sort_unstable();
    entries.dedup();
    Ok(entries)
}

fn table_base_states(
    instructions: &[Instruction],
    edges: &[Vec<usize>],
    entries: &[usize],
    register: Register,
) -> Vec<Option<u64>> {
    let mut states = vec![None; instructions.len()];
    let mut seen = vec![false; instructions.len()];
    let mut pending = entries.to_vec();
    for &entry in entries {
        seen[entry] = true;
    }
    let mut info = InstructionInfoFactory::new();
    while let Some(at) = pending.pop() {
        let instruction = &instructions[at];
        let call = matches!(
            instruction.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        );
        let internal_call = instruction.is_call_near()
            && in_range(
                instruction.near_branch_target(),
                instructions[0].ip(),
                instructions.last().unwrap().next_ip(),
            );
        let preserved = matches!(
            register,
            Register::RBX
                | Register::RBP
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        );
        let outgoing = if instruction.mnemonic() == Mnemonic::Lea
            && instruction.op0_register() == register
            && instruction.is_ip_rel_memory_operand()
        {
            Some(instruction.ip_rel_memory_address())
        } else if writes_register(&mut info, instruction, register)
            || (call && (internal_call || !preserved))
        {
            None
        } else {
            states[at]
        };
        for &other in &edges[at] {
            let joined = if !seen[other] || states[other] == outgoing {
                outgoing
            } else {
                None
            };
            if !seen[other] || states[other] != joined {
                seen[other] = true;
                states[other] = joined;
                pending.push(other);
            }
        }
    }
    states
}

fn table_successors(
    instructions: &[Instruction],
    indirect: &BTreeMap<u64, Vec<u64>>,
) -> Result<Vec<Vec<usize>>> {
    let start = instructions[0].ip();
    let end = instructions.last().unwrap().next_ip();
    let addresses: BTreeMap<_, _> = instructions
        .iter()
        .enumerate()
        .map(|(at, i)| (i.ip(), at))
        .collect();
    let mut edges = vec![Vec::new(); instructions.len()];
    for (at, instruction) in instructions.iter().enumerate() {
        let mut targets = Vec::new();
        match instruction.flow_control() {
            FlowControl::Next | FlowControl::Call | FlowControl::IndirectCall => {
                targets.push(instruction.next_ip())
            }
            FlowControl::ConditionalBranch => {
                targets.extend([instruction.next_ip(), instruction.near_branch_target()])
            }
            FlowControl::UnconditionalBranch => targets.push(instruction.near_branch_target()),
            FlowControl::IndirectBranch => {
                targets.extend(
                    indirect
                        .get(&instruction.ip())
                        .ok_or("unresolved table control flow")?
                        .iter()
                        .copied(),
                );
            }
            FlowControl::Return => {}
            _ => return Err("unsupported relative-table control flow".into()),
        }
        for target in targets {
            if in_range(target, start, end) {
                edges[at].push(
                    *addresses
                        .get(&target)
                        .ok_or("table control flow enters an instruction")?,
                );
            }
        }
        edges[at].sort_unstable();
        edges[at].dedup();
    }
    Ok(edges)
}

fn table_flags_dead(instructions: &[Instruction], edges: &[Vec<usize>], jump: usize) -> bool {
    let mut live = vec![0; instructions.len()];
    let mut pending = vec![jump];
    live[jump] = instructions[jump - 1].rflags_modified();
    while let Some(at) = pending.pop() {
        let instruction = &instructions[at];
        if instruction.rflags_read() & live[at] != 0 {
            return false;
        }
        // A zero repeat/shift count leaves the incoming flags intact.
        let conditional = instruction.has_rep_prefix()
            || instruction.has_repne_prefix()
            || (matches!(
                instruction.mnemonic(),
                Mnemonic::Shl
                    | Mnemonic::Shr
                    | Mnemonic::Sar
                    | Mnemonic::Shld
                    | Mnemonic::Shrd
                    | Mnemonic::Rol
                    | Mnemonic::Ror
                    | Mnemonic::Rcl
                    | Mnemonic::Rcr
            ) && (0..instruction.op_count()).any(|op| {
                instruction.op_kind(op) == OpKind::Register
                    && instruction.op_register(op) == Register::CL
            }));
        let overwritten = if conditional {
            0
        } else {
            instruction.rflags_modified()
        };
        let remaining = live[at] & !overwritten;
        if remaining == 0 {
            continue;
        }
        if matches!(
            instruction.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            if instruction.is_call_near()
                && in_range(
                    instruction.near_branch_target(),
                    instructions[0].ip(),
                    instructions.last().unwrap().next_ip(),
                )
            {
                return false;
            }
            // Arithmetic flags are neither inputs nor outputs in the SysV ABI.
            continue;
        }
        for &other in &edges[at] {
            let joined = live[other] | remaining;
            if joined != live[other] {
                live[other] = joined;
                pending.push(other);
            }
        }
    }
    true
}

fn multiple_relative_tables(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<Vec<JumpTable>> {
    let mut candidates = BTreeMap::new();
    for (at, instruction) in instructions.iter().enumerate() {
        if instruction.flow_control() == FlowControl::IndirectBranch {
            let tables =
                relative_table_candidates(binary, index, instructions, at, ips, start, end)?;
            if tables.is_empty() {
                return Err(Error::Unsupported(format!(
                    "no relative table candidate at 0x{:x}",
                    instruction.ip()
                )));
            }
            candidates.insert(at, tables);
        }
    }
    let entries = table_entries(index, instructions, start, end)?;
    // Prove bases against all candidate edges, before selecting any table.
    let indirect = candidates
        .iter()
        .map(|(&at, tables)| {
            (
                instructions[at].ip(),
                tables
                    .iter()
                    .flat_map(|t| t.targets.iter().copied())
                    .collect(),
            )
        })
        .collect();
    let edges = table_successors(instructions, &indirect)?;
    let mut states = BTreeMap::new();
    let mut tables = Vec::new();
    for (at, choices) in candidates {
        let register = choices[0].setup.as_ref().unwrap().register;
        let known = states
            .entry(register)
            .or_insert_with(|| table_base_states(instructions, &edges, &entries, register));
        let table = choices
            .into_iter()
            .find(|table| {
                [at - 2, at - 1, at]
                    .iter()
                    .all(|&site| known[site] == Some(table.original_base))
            })
            .ok_or_else(|| {
                Error::Unsupported(format!(
                    "relative table base is not proven at 0x{:x}",
                    instructions[at].ip()
                ))
            })?;
        tables.push(table);
    }
    Ok(tables)
}

fn jump_table_absolute(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Result<JumpTable> {
    let jump = instructions[at];
    let unsupported =
        || Error::Unsupported(format!("unsupported indirect jump at 0x{:x}", jump.ip()));
    let raw = binary.content_from_virtual_address(jump.ip(), jump.len() as u64);
    let sib = match raw {
        [0xff, 0x24, sib, _, _, _, _] if jump.segment_prefix() == Register::None => *sib,
        [0x3e, 0xff, 0x24, sib, _, _, _, _] if jump.segment_prefix() == Register::DS => *sib,
        [0x3e, 0x42, 0xff, 0x24, sib, _, _, _, _] if jump.segment_prefix() == Register::DS => *sib,
        _ => return Err(unsupported()),
    };
    if binary.header().file_type() != header::FileType::EXEC
        || jump.op0_kind() != OpKind::Memory
        || jump.memory_base() != Register::None
        || jump.memory_index() == Register::None
        || jump.memory_index_scale() != 8
        || jump.memory_displ_size() != 8
        || sib & 0xc7 != 0xc5
    {
        return Err(unsupported());
    }
    let guard = guarded_index(
        index,
        instructions,
        at,
        at,
        jump.memory_index().full_register(),
    )
    .ok_or_else(unsupported)?;
    let base = jump.memory_displacement64();
    let byte_len = (guard.bound + 1) * 8;
    let table_end = base.checked_add(byte_len).ok_or_else(unsupported)?;
    if !binary.segments().any(|seg| {
        seg.p_type() == segment::Type::LOAD
            && seg.flags() & segment::Flags::R.bits() != 0
            && seg.flags() & (segment::Flags::W | segment::Flags::X).bits() == 0
            && base >= seg.virtual_address()
            && table_end <= seg.virtual_address().saturating_add(seg.physical_size())
    }) || index
        .relocation_sites
        .range(base.saturating_sub(7)..table_end)
        .next()
        .is_some()
        || index
            .relocation_targets
            .range(base..table_end)
            .next()
            .is_some()
        || index.references.range(base..table_end).any(|(_, sources)| {
            sources
                .iter()
                .any(|site| site.source != jump.ip() || site.direct)
        })
        || other_table_use(
            instructions,
            jump.ip(),
            None,
            Register::None,
            base,
            table_end,
        )
    {
        return Err(unsupported());
    }
    let content = binary.content_from_virtual_address(base, byte_len);
    if content.len() != byte_len as usize {
        return Err(unsupported());
    }
    let mut targets = Vec::with_capacity(guard.bound as usize + 1);
    for word in content.chunks_exact(8) {
        let target = u64::from_le_bytes(word.try_into().unwrap());
        if !binary.segments().any(|seg| {
            seg.p_type() == segment::Type::LOAD
                && seg.flags() & segment::Flags::X.bits() != 0
                && in_range(
                    target,
                    seg.virtual_address(),
                    seg.virtual_address().saturating_add(seg.physical_size()),
                )
        }) || (in_range(target, start, end)
            && (!ips.contains(&target) || in_range(target, guard.branch, jump.next_ip())))
        {
            return Err(unsupported());
        }
        targets.push(target);
    }
    Ok(JumpTable {
        lea: jump.ip(),
        jump: jump.ip(),
        guard: guard.branch,
        targets,
        setup: None,
        kind: TableKind::Absolute,
        original_base: base,
    })
}

fn immutable_pointers(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    base: u64,
    count: u64,
    start: u64,
    end: u64,
    reference_source: Option<u64>,
) -> Option<Vec<u64>> {
    let len = count.checked_mul(8)?;
    let table_end = base.checked_add(len)?;
    let plain = binary.header().file_type() == header::FileType::EXEC
        && binary.segments().any(|seg| {
            seg.p_type() == segment::Type::LOAD
                && seg.flags() & segment::Flags::R.bits() != 0
                && seg.flags() & (segment::Flags::W | segment::Flags::X).bits() == 0
                && base >= seg.virtual_address()
                && table_end <= seg.virtual_address().saturating_add(seg.physical_size())
        })
        && index
            .relocation_sites
            .range(base.saturating_sub(7)..table_end)
            .next()
            .is_none();
    let relro = binary.header().file_type() == header::FileType::DYN
        && binary.segments().any(|seg| {
            seg.p_type() == segment::Type::GNU_RELRO
                && base >= seg.virtual_address()
                && table_end <= (seg.virtual_address().saturating_add(seg.virtual_size()) & !0xfff)
        })
        && binary.segments().any(|seg| {
            seg.p_type() == segment::Type::LOAD
                && seg.flags() & segment::Flags::R.bits() != 0
                && base >= seg.virtual_address()
                && table_end <= seg.virtual_address().saturating_add(seg.physical_size())
        });
    if !plain && !relro {
        return None;
    }
    if index
        .relocation_targets
        .range(base..table_end)
        .next()
        .is_some()
    {
        return None;
    }
    if relro {
        if index
            .relocation_sites
            .range(base.saturating_sub(7)..base)
            .next()
            .is_some()
        {
            return None;
        }
        let sites: Vec<_> = index
            .relocation_sites
            .range(base..table_end)
            .copied()
            .collect();
        let expected: Vec<_> = (0..count).map(|slot| base + slot * 8).collect();
        if sites != expected {
            return None;
        }
    }
    if index.references.range(base..table_end).any(|(_, sources)| {
        sources.iter().any(|site| {
            Some(site.source) != reference_source
                || site.direct
                || !in_range(site.source, start, end)
        })
    }) {
        return None;
    }
    let content = binary.content_from_virtual_address(base, len);
    if content.len() != len as usize {
        return None;
    }
    let mut targets = Vec::with_capacity(count as usize);
    for (slot, word) in content.chunks_exact(8).enumerate() {
        let address = base + (slot * 8) as u64;
        let target = if plain {
            u64::from_le_bytes(word.try_into().ok()?)
        } else {
            index.relative_slots.get(&address).copied().flatten()?
        };
        if !binary.segments().any(|seg| {
            seg.p_type() == segment::Type::LOAD
                && seg.flags() & segment::Flags::X.bits() != 0
                && in_range(
                    target,
                    seg.virtual_address(),
                    seg.virtual_address().saturating_add(seg.physical_size()),
                )
        }) {
            return None;
        }
        targets.push(target);
    }
    Some(targets)
}

fn other_table_use(
    instructions: &[Instruction],
    load_ip: u64,
    lea_ip: Option<u64>,
    base_reg: Register,
    table_base: u64,
    table_end: u64,
) -> bool {
    let mut info = InstructionInfoFactory::new();
    instructions.iter().any(|instruction| {
        if instruction.ip() == load_ip || Some(instruction.ip()) == lea_ip {
            return false;
        }
        if base_reg != Register::None
            && info
                .info(instruction)
                .used_registers()
                .iter()
                .any(|used| used.register().full_register() == base_reg)
        {
            return true;
        }
        (0..instruction.op_count()).any(|operand| {
            let kind = instruction.op_kind(operand);
            let value = match kind {
                OpKind::Memory if instruction.is_ip_rel_memory_operand() => {
                    Some(instruction.ip_rel_memory_address())
                }
                OpKind::Memory => Some(instruction.memory_displacement64()),
                OpKind::Immediate64 => Some(instruction.immediate64()),
                OpKind::Immediate32 => Some(u64::from(instruction.immediate32())),
                OpKind::Immediate32to64 => Some(instruction.immediate32to64() as u64),
                _ => None,
            };
            value.is_some_and(|value| in_range(value, table_base, table_end))
        })
    })
}

fn register_jump_notrack(binary: &elf::Binary, jump: Instruction) -> Option<bool> {
    let bytes = binary.content_from_virtual_address(jump.ip(), jump.len() as u64);
    let notrack = match bytes {
        [0xff, modrm] if modrm & 0xf8 == 0xe0 => false,
        [rex, 0xff, modrm] if (0x40..=0x4f).contains(rex) && modrm & 0xf8 == 0xe0 => false,
        [0x3e, 0xff, modrm] if modrm & 0xf8 == 0xe0 => true,
        [0x3e, rex, 0xff, modrm] if (0x40..=0x4f).contains(rex) && modrm & 0xf8 == 0xe0 => true,
        _ => return None,
    };
    (jump.segment_prefix()
        == if notrack {
            Register::DS
        } else {
            Register::None
        })
    .then_some(notrack)
}

fn fixed_pointer_jump(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Option<u64> {
    if at == 0 {
        return None;
    }
    let jump = instructions[at];
    let load = instructions[at - 1];
    if register_jump_notrack(binary, jump).is_none()
        || jump.op0_kind() != OpKind::Register
        || load.mnemonic() != Mnemonic::Mov
        || load.op0_kind() != OpKind::Register
        || load.op1_kind() != OpKind::Memory
        || load.op0_register() != jump.op0_register()
        || load.op0_register().size() != 8
        || !load.is_ip_rel_memory_operand()
        || load.segment_prefix() != Register::None
        || load.next_ip() != jump.ip()
        || index
            .references
            .range(jump.ip()..=jump.ip())
            .next()
            .is_some()
    {
        return None;
    }
    let target = *immutable_pointers(
        binary,
        index,
        load.ip_rel_memory_address(),
        1,
        start,
        end,
        Some(load.ip()),
    )?
    .first()?;
    if other_table_use(
        instructions,
        load.ip(),
        None,
        Register::None,
        load.ip_rel_memory_address(),
        load.ip_rel_memory_address().checked_add(8)?,
    ) {
        return None;
    }
    if in_range(target, start, end) && (!ips.contains(&target) || target == jump.ip()) {
        return None;
    }
    Some(target)
}

fn indexed_pointer_jump(
    binary: &elf::Binary,
    index: &AnalysisIndex,
    instructions: &[Instruction],
    at: usize,
    ips: &BTreeSet<u64>,
    start: u64,
    end: u64,
) -> Option<IndexedDispatch> {
    if at < 2 || binary.header().file_type() != header::FileType::EXEC {
        return None;
    }
    let jump = instructions[at];
    let load = instructions[at - 1];
    let notrack = register_jump_notrack(binary, jump)?;
    if jump.op0_kind() != OpKind::Register
        || load.mnemonic() != Mnemonic::Mov
        || load.op0_kind() != OpKind::Register
        || load.op1_kind() != OpKind::Memory
        || load.op0_register() != jump.op0_register()
        || load.op0_register().size() != 8
        || load.memory_index() == Register::None
        || load.memory_index_scale() != 8
        || load.segment_prefix() != Register::None
        || load.next_ip() != jump.ip()
        || index
            .references
            .range(jump.ip()..=jump.ip())
            .next()
            .is_some()
    {
        return None;
    }
    let destination = jump.op0_register().full_register();
    let index_reg = load.memory_index().full_register();
    let base_reg = load.memory_base().full_register();
    if index_reg == destination || base_reg == destination || base_reg == index_reg {
        return None;
    }
    let guard = guarded_index(index, instructions, at - 1, at, index_reg)?;
    let mut candidates = Vec::new();
    if load.memory_base() == Register::None {
        candidates.push((load.memory_displacement64(), None));
    } else {
        for lea in instructions[..at - 1].iter().rev() {
            if lea.mnemonic() == Mnemonic::Lea
                && lea.op0_kind() == OpKind::Register
                && lea.op0_register().full_register() == base_reg
                && lea.is_ip_rel_memory_operand()
            {
                let base = u64::try_from(
                    lea.ip_rel_memory_address() as i128
                        + load.memory_displacement64() as i64 as i128,
                )
                .ok()?;
                candidates.push((base, Some(lea.ip())));
            }
        }
    }
    for (base, lea) in candidates {
        let table_end = base.checked_add((guard.bound + 1) * 8)?;
        if other_table_use(instructions, load.ip(), lea, base_reg, base, table_end) {
            continue;
        }
        let Some(targets) = immutable_pointers(
            binary,
            index,
            base,
            guard.bound + 1,
            start,
            end,
            Some(lea.unwrap_or(load.ip())),
        ) else {
            continue;
        };
        if targets.iter().any(|&target| {
            in_range(target, start, end)
                && (!ips.contains(&target) || in_range(target, guard.branch, jump.next_ip()))
        }) {
            continue;
        }
        if let Some(lea) = lea {
            let entries = table_entries(index, instructions, start, end).ok()?;
            let indirect = BTreeMap::from([(jump.ip(), targets.clone())]);
            let edges = table_successors(instructions, &indirect).ok()?;
            let known = table_base_states(instructions, &edges, &entries, base_reg);
            let initializer = instructions
                .binary_search_by_key(&lea, Instruction::ip)
                .ok()?;
            let expected = Some(instructions[initializer].ip_rel_memory_address());
            if known[at - 1] != expected || known[at] != expected {
                continue;
            }
        }
        return Some(IndexedDispatch {
            jump,
            guard: guard.branch,
            targets,
            index: index_reg,
            notrack,
            original_base: base,
            original_bytes: binary
                .content_from_virtual_address(base, (guard.bound + 1) * 8)
                .to_vec(),
        });
    }
    None
}

fn analyze(binary: &elf::Binary, index: &AnalysisIndex, start: u64, size: u64) -> Result<Function> {
    if !(5..=1_048_576).contains(&size) {
        return Err("function size must be between 5 bytes and 1 MiB".into());
    }
    let end = start.checked_add(size).ok_or("function address overflow")?;
    let mapped = binary.segments().any(|s| {
        s.p_type() == segment::Type::LOAD
            && s.flags() & segment::Flags::X.bits() != 0
            && start >= s.virtual_address()
            && end <= s.virtual_address().saturating_add(s.physical_size())
    });
    if !mapped {
        return Err("function is not fully inside an executable PT_LOAD".into());
    }
    let fallthrough_mapped = binary.segments().any(|s| {
        s.p_type() == segment::Type::LOAD
            && s.flags() & segment::Flags::X.bits() != 0
            && in_range(
                end,
                s.virtual_address(),
                s.virtual_address().saturating_add(s.physical_size()),
            )
    });
    let bytes = binary.content_from_virtual_address(start, size);
    if bytes.len() != size as usize {
        return Err("cannot read complete function".into());
    }
    if let Some(site) = index.relocation_sites.range(start..end).next() {
        return Err(format!("relocation inside selected function at 0x{site:x}").into());
    }
    let unwind = index.unwind_for(binary, start, end)?;

    let mut decoder = Decoder::with_ip(64, bytes, start, DecoderOptions::NONE);
    let mut instructions = Vec::new();
    let mut boundaries = BTreeSet::new();
    let mut ips = BTreeSet::new();
    while decoder.can_decode() {
        let instr = decoder.decode();
        if instr.is_invalid() {
            return Err(format!("invalid instruction at 0x{:x}", instr.ip()).into());
        }
        ips.insert(instr.ip());
        if instr.is_ip_rel_memory_operand() && in_range(instr.ip_rel_memory_address(), start, end) {
            return Err(format!(
                "RIP-relative reference into selected function at 0x{:x}",
                instr.ip()
            )
            .into());
        }
        match instr.flow_control() {
            FlowControl::Next | FlowControl::IndirectCall => {}
            FlowControl::Call if instr.is_call_near() => {
                if in_range(instr.near_branch_target(), start, end) {
                    boundaries.insert(instr.near_branch_target());
                }
            }
            FlowControl::ConditionalBranch if instr.is_jcc_short_or_near() => {
                let target = instr.near_branch_target();
                if in_range(target, start, end) {
                    boundaries.insert(target);
                }
                if instr.next_ip() < end {
                    boundaries.insert(instr.next_ip());
                }
            }
            FlowControl::UnconditionalBranch if instr.is_jmp_short_or_near() => {
                let target = instr.near_branch_target();
                if in_range(target, start, end) {
                    boundaries.insert(target);
                }
                if instr.next_ip() < end {
                    boundaries.insert(instr.next_ip());
                }
            }
            FlowControl::IndirectBranch => {
                if instr.next_ip() < end {
                    boundaries.insert(instr.next_ip());
                }
            }
            FlowControl::Return if instr.mnemonic() == Mnemonic::Ret => {
                if instr.next_ip() < end {
                    boundaries.insert(instr.next_ip());
                }
            }
            _ => {
                return Err(format!("unsupported control transfer at 0x{:x}", instr.ip()).into());
            }
        }
        instructions.push(instr);
    }
    let mut unresolved = None;
    let mut tables = Vec::new();
    let mut dispatches = Vec::new();
    let mut fixed_jumps = BTreeMap::new();
    let mut fixed_slots = BTreeSet::new();
    let mut allowed_relocation_sites = BTreeSet::new();
    for (at, instruction) in instructions.iter().enumerate() {
        if instruction.flow_control() == FlowControl::IndirectBranch {
            if let Ok(table) = jump_table(binary, index, &instructions, at, &ips, start, end) {
                boundaries.extend(
                    table
                        .targets
                        .iter()
                        .copied()
                        .filter(|&target| in_range(target, start, end)),
                );
                tables.push(table);
            } else if let Some(target) =
                fixed_pointer_jump(binary, index, &instructions, at, &ips, start, end)
            {
                let slot = instructions[at - 1].ip_rel_memory_address();
                if index.relative_slots.get(&slot).is_some_and(Option::is_some)
                    && in_range(target, start, end)
                {
                    allowed_relocation_sites.insert(slot);
                }
                boundaries.extend(in_range(target, start, end).then_some(target));
                fixed_jumps.insert(instruction.ip(), target);
                fixed_slots.insert(slot);
            } else if let Some(dispatch) =
                indexed_pointer_jump(binary, index, &instructions, at, &ips, start, end)
            {
                boundaries.extend(
                    dispatch
                        .targets
                        .iter()
                        .copied()
                        .filter(|&target| in_range(target, start, end)),
                );
                dispatches.push(dispatch);
            } else {
                unresolved.get_or_insert(instruction.ip());
            }
        }
    }
    if let Some(jump) = unresolved {
        if instructions
            .iter()
            .filter(|i| i.flow_control() == FlowControl::IndirectBranch)
            .count()
            < 2
        {
            return Err(format!("unsupported indirect jump at 0x{jump:x}").into());
        }
        tables = multiple_relative_tables(binary, index, &instructions, &ips, start, end)?;
        dispatches.clear();
        fixed_jumps.clear();
        fixed_slots.clear();
        allowed_relocation_sites.clear();
        boundaries.extend(
            tables
                .iter()
                .flat_map(|table| table.targets.iter().copied()),
        );
    }
    if tables.iter().any(|table| table.kind == TableKind::Relative) {
        let indirect = tables
            .iter()
            .map(|table| (table.jump, table.targets.clone()))
            .chain(dispatches.iter().map(|d| (d.jump.ip(), d.targets.clone())))
            .chain(
                fixed_jumps
                    .iter()
                    .map(|(&jump, &target)| (jump, vec![target])),
            )
            .collect();
        let edges = table_successors(&instructions, &indirect)?;
        for table in tables
            .iter()
            .filter(|table| table.kind == TableKind::Relative)
        {
            let at = instructions
                .binary_search_by_key(&table.jump, Instruction::ip)
                .map_err(|_| "jump table instruction missing")?;
            // Relocating the dispatch ADD can change its arithmetic flags.
            if !table_flags_dead(&instructions, &edges, at) {
                return Err(Error::Unsupported(format!(
                    "relative table flags remain live at 0x{:x}",
                    table.jump
                )));
            }
        }
    }
    let computed_targets: Vec<_> = tables
        .iter()
        .flat_map(|table| table.targets.iter().copied())
        .chain(
            dispatches
                .iter()
                .flat_map(|dispatch| dispatch.targets.iter().copied()),
        )
        .chain(fixed_jumps.values().copied())
        .collect();
    for table in &tables {
        let jump_end = instructions
            .iter()
            .find(|instruction| instruction.ip() == table.jump)
            .ok_or("jump table instruction missing")?
            .next_ip();
        if computed_targets
            .iter()
            .any(|&target| in_range(target, table.guard, jump_end))
        {
            return Err(format!("computed target bypasses guard at 0x{:x}", table.jump).into());
        }
    }
    for dispatch in &dispatches {
        if computed_targets
            .iter()
            .any(|&target| in_range(target, dispatch.guard, dispatch.jump.next_ip()))
        {
            return Err(format!(
                "computed target bypasses guard at 0x{:x}",
                dispatch.jump.ip()
            )
            .into());
        }
    }
    let entry_labels = index.check(start, end, &allowed_relocation_sites)?;
    boundaries.extend(entry_labels.iter().copied());
    if let Some(rows) = &unwind
        && rows.iter().any(|(ip, _)| !ips.contains(ip))
    {
        return Err("unwind row is not an instruction boundary".into());
    }
    if !boundaries.iter().all(|ip| ips.contains(ip)) {
        return Err("branch lands inside an instruction".into());
    }
    let starts: Vec<u64> = boundaries.into_iter().collect();
    let mut blocks = Vec::new();
    let mut cursor = 0;
    for (i, &old) in starts.iter().enumerate() {
        let stop = starts.get(i + 1).copied().unwrap_or(end);
        let first = cursor;
        while cursor < instructions.len() && instructions[cursor].ip() < stop {
            cursor += 1;
        }
        if first == cursor {
            return Err(format!("empty block at 0x{old:x}").into());
        }
        let mut body = instructions[first..cursor].to_vec();
        let last = *body.last().unwrap();
        let exit = match last.flow_control() {
            FlowControl::ConditionalBranch => {
                body.pop();
                if last.next_ip() >= end {
                    return Err("conditional branch falls outside function".into());
                }
                Exit::Branch {
                    target: last.near_branch_target(),
                    fallthrough: last.next_ip(),
                    cc: last.condition_code(),
                }
            }
            FlowControl::UnconditionalBranch => {
                body.pop();
                Exit::Jump(last.near_branch_target())
            }
            FlowControl::IndirectBranch => {
                if let Some(&target) = fixed_jumps.get(&last.ip()) {
                    body.pop();
                    Exit::Jump(target)
                } else if let Some(index) = dispatches
                    .iter()
                    .position(|dispatch| dispatch.jump.ip() == last.ip())
                {
                    body.pop();
                    Exit::Dispatch(index)
                } else {
                    Exit::Table(
                        tables
                            .iter()
                            .position(|table| table.jump == last.ip())
                            .ok_or("missing jump table")?,
                    )
                }
            }
            FlowControl::Return => Exit::Return,
            _ => {
                if stop == end && !fallthrough_mapped {
                    return Err("function falls through outside an executable PT_LOAD".into());
                }
                Exit::Fallthrough(stop)
            }
        };
        let tail = match exit {
            Exit::Branch { .. } => 11,
            Exit::Jump(_) | Exit::Fallthrough(_) | Exit::Dispatch(_) => 5,
            Exit::Return => 0,
            Exit::Table(index) => usize::from(tables[index].setup.is_some()) * 7,
        };
        let len = body.iter().map(|x| x.len()).sum::<usize>()
            + body
                .iter()
                .filter(|ins| {
                    tables
                        .iter()
                        .any(|table| table.setup.is_some_and(|setup| setup.load == ins.ip()))
                })
                .count()
                * 7
            + tail;
        blocks.push(Block {
            old,
            body,
            exit,
            len,
        });
    }
    let block_ips: BTreeSet<u64> = blocks.iter().map(|b| b.old).collect();
    for block in &blocks {
        let targets: Vec<u64> = match block.exit {
            Exit::Branch {
                target,
                fallthrough,
                ..
            } => vec![target, fallthrough],
            Exit::Jump(target) | Exit::Fallthrough(target) => vec![target],
            Exit::Return => vec![],
            Exit::Table(index) => tables[index].targets.clone(),
            Exit::Dispatch(index) => dispatches[index].targets.clone(),
        };
        for target in targets {
            if in_range(target, start, end) && !block_ips.contains(&target) {
                return Err(format!("edge enters middle of block at 0x{target:x}").into());
            }
        }
    }

    let mut entries = Vec::new();
    for &label in &entry_labels {
        let offset = (label - start) as usize;
        let endbr = bytes[offset..].starts_with(&ENDBR64);
        let mut sources = Vec::new();
        if label != start
            && !endbr
            && let Some(refs) = index.references.get(&label)
        {
            for site in refs
                .iter()
                .filter(|site| !in_range(site.source, start, end))
            {
                let Some(at) = site.offset else { break };
                if site.source < start && site.next > start {
                    break;
                }
                let address = site.source + at as u64;
                if at + 4 > (site.next - site.source) as usize
                    || index
                        .relocation_sites
                        .range(address..address + 4)
                        .next()
                        .is_some()
                {
                    break;
                }
                let original = binary.content_from_virtual_address(address, 4);
                let Ok(original) = <[u8; 4]>::try_from(original) else {
                    break;
                };
                sources.push(SourcePatch {
                    source: site.source,
                    address,
                    next: site.next,
                    original,
                });
            }
            if sources.len()
                == refs
                    .iter()
                    .filter(|site| !in_range(site.source, start, end))
                    .count()
            {
                entries.push(EntryPatch {
                    label,
                    window: None,
                    sources,
                });
                continue;
            }
            sources.clear();
        }
        let patch = label + u64::from(endbr) * 4;
        let mut len = 0;
        for instr in instructions.iter().filter(|instr| instr.ip() >= patch) {
            len += instr.len();
            if len >= 5 {
                break;
            }
        }
        if len < 5 || patch + len as u64 > end {
            return Err(format!(
                "entry at 0x{label:x} has insufficient instruction bytes for a direct jump"
            )
            .into());
        }
        entries.push(EntryPatch {
            label,
            window: Some((patch, len)),
            sources,
        });
    }
    let patched: Vec<_> = entries
        .iter()
        .filter(|entry| entry.window.is_some())
        .collect();
    for pair in patched.windows(2) {
        let (patch, len) = pair[0].window.unwrap();
        if patch + len as u64 > pair[1].label {
            return Err("entry patch windows overlap".into());
        }
    }
    for entry in patched {
        let (patch, len) = entry.window.unwrap();
        let protected = if patch == entry.label {
            patch + 1
        } else {
            patch
        };
        if let Some((&target, _)) =
            index
                .references
                .range(protected..patch + len as u64)
                .find(|entry| {
                    let (&target, sources) = *entry;
                    sources
                        .iter()
                        .any(|site| !in_range(site.source, start, end))
                        && !entries
                            .iter()
                            .any(|entry| entry.label == target && entry.window.is_none())
                })
        {
            return Err(format!("reference enters entry patch window at 0x{target:x}").into());
        }
        if let Some(&target) = index
            .relocation_targets
            .range(patch + 1..patch + len as u64)
            .next()
        {
            return Err(format!("relocation enters entry patch window at 0x{target:x}").into());
        }
    }
    Ok(Function {
        start,
        end,
        bytes: bytes.to_vec(),
        entries,
        blocks,
        tables,
        dispatches,
        fixed_targets: fixed_jumps.values().copied().collect(),
        fixed_slots: fixed_slots.into_iter().collect(),
        unwind,
    })
}

fn condition_opcode(cc: ConditionCode) -> Result<u8> {
    Ok(match cc {
        ConditionCode::o => 0x80,
        ConditionCode::no => 0x81,
        ConditionCode::b => 0x82,
        ConditionCode::ae => 0x83,
        ConditionCode::e => 0x84,
        ConditionCode::ne => 0x85,
        ConditionCode::be => 0x86,
        ConditionCode::a => 0x87,
        ConditionCode::s => 0x88,
        ConditionCode::ns => 0x89,
        ConditionCode::p => 0x8a,
        ConditionCode::np => 0x8b,
        ConditionCode::l => 0x8c,
        ConditionCode::ge => 0x8d,
        ConditionCode::le => 0x8e,
        ConditionCode::g => 0x8f,
        _ => return Err("unsupported condition code".into()),
    })
}

fn rel32(from_next: u64, target: u64) -> Result<[u8; 4]> {
    let delta = target as i128 - from_next as i128;
    let value = i32::try_from(delta)
        .map_err(|_| format!("relative branch out of range: 0x{from_next:x} -> 0x{target:x}"))?;
    Ok(value.to_le_bytes())
}

fn destination(
    target: u64,
    function: &Function,
    moved: &BTreeMap<u64, u64>,
    entries: &BTreeMap<u64, u64>,
) -> Result<u64> {
    if in_range(target, function.start, function.end) {
        moved
            .get(&target)
            .copied()
            .ok_or_else(|| Error::Invariant(format!("unmapped branch target 0x{target:x}")))
    } else {
        Ok(entries.get(&target).copied().unwrap_or(target))
    }
}

fn function_seed(seed: u64, start: u64) -> u64 {
    let mut value = seed ^ start ^ 0x6a09e667f3bcc909;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
    value ^ (value >> 31)
}

fn permute_all(len: usize, seed: u64) -> Vec<usize> {
    let mut order: Vec<usize> = (0..len).collect();
    let mut state = seed ^ 0xd1b54a32d192ed03;
    for i in (1..len).rev() {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        let value = state.wrapping_mul(0x2545f4914f6cdd1d);
        order.swap(i, value as usize % (i + 1));
    }
    order
}

const ENDBR64: [u8; 4] = [0xf3, 0x0f, 0x1e, 0xfa];

struct Encoded {
    code: Vec<u8>,
    moved: BTreeMap<u64, u64>,
    lengths: BTreeMap<u64, usize>,
}

fn needs_endbr(function: &Function, block: &Block) -> bool {
    let offset = (block.old - function.start) as usize;
    !function.bytes[offset..].starts_with(&ENDBR64)
}

fn fragment_endbr(function: &Function, block: &Block, scratch: Scratch) -> bool {
    scratch.saved() != 0 || needs_endbr(function, block)
}

fn encoded_capacity(function: &Function) -> Result<usize> {
    Ok(function.blocks.iter().try_fold(0usize, |sum, block| {
        sum.checked_add(block.len).ok_or("clone length overflow")
    })?)
}

fn entry_offset(function: &Function, seed: u64, label: u64) -> Result<usize> {
    let mut offset = 0usize;
    for index in permute_all(function.blocks.len(), seed) {
        let block = &function.blocks[index];
        if block.old == label {
            return Ok(offset);
        }
        offset = offset
            .checked_add(block.len)
            .ok_or("clone length overflow")?;
    }
    Err("entry block missing".into())
}

struct RewriteTargets<'a> {
    moved: &'a BTreeMap<u64, u64>,
    entries: &'a BTreeMap<u64, u64>,
    tables: &'a BTreeMap<u64, u64>,
    references: Option<&'a BTreeMap<u64, ReferenceSite>>,
    calls: Option<&'a BTreeMap<u64, CallSite>>,
}

fn write_body(
    function: &Function,
    block: &Block,
    base: u64,
    code: &mut Vec<u8>,
    targets: &RewriteTargets<'_>,
    state: Option<(u64, Scratch)>,
) -> Result<()> {
    for instr in &block.body {
        if let Some(setup) = function
            .tables
            .iter()
            .filter_map(|table| table.setup)
            .find(|setup| setup.load == instr.ip())
        {
            let clone = targets
                .tables
                .get(&instr.ip())
                .copied()
                .ok_or("missing cloned jump table")?;
            rip_lea_register(code, base, setup.register, clone)?;
        }
        if let Some(setup) = function
            .tables
            .iter()
            .find(|table| table.jump == instr.ip())
            .and_then(|table| table.setup)
        {
            rip_lea_register(code, base, setup.register, setup.original)?;
        }
        let address = base + code.len() as u64;
        if let Some(site) = targets.references.and_then(|sites| sites.get(&instr.ip())) {
            if let Some(slot) = state.and_then(|(_, scratch)| scratch.r10) {
                movq_to_xmm(code, slot, 10);
            }
            code.extend_from_slice(&reference_code(
                instr,
                base + code.len() as u64,
                site.va,
                site.key,
            )?);
            if let Some(slot) = state.and_then(|(_, scratch)| scratch.r10) {
                movq_from_xmm(code, slot, 10);
            }
        } else if instr.is_ip_rel_memory_operand()
            || function
                .tables
                .iter()
                .any(|table| table.kind == TableKind::Absolute && table.jump == instr.ip())
            || (instr.flow_control() == FlowControl::Call && instr.is_call_near())
        {
            let mut relocated = *instr;
            if let Some(&table) = targets.tables.get(&instr.ip())
                && (instr.is_ip_rel_memory_operand()
                    || instr.flow_control() == FlowControl::IndirectBranch)
            {
                relocated.set_memory_displacement64(table);
            }
            if instr.flow_control() == FlowControl::Call && instr.is_call_near() {
                let target = instr.near_branch_target();
                let destination =
                    if let Some(site) = targets.calls.and_then(|sites| sites.get(&instr.ip())) {
                        site.va
                    } else {
                        match targets.entries.get(&target) {
                            Some(&entry) => entry,
                            None => destination(target, function, targets.moved, targets.entries)?,
                        }
                    };
                relocated.set_near_branch64(destination);
            }
            let encoded = BlockEncoder::encode(
                64,
                InstructionBlock::new(std::slice::from_ref(&relocated), address),
                BlockEncoderOptions::NONE,
            )
            .map_err(|e| format!("cannot relocate instruction 0x{:x}: {e}", instr.ip()))?;
            if encoded.code_buffer.len() != instr.len() {
                return Err(format!("instruction 0x{:x} changed width", instr.ip()).into());
            }
            if targets.tables.contains_key(&instr.ip())
                && instr.flow_control() == FlowControl::IndirectBranch
            {
                let decoded =
                    Decoder::with_ip(64, &encoded.code_buffer, address, DecoderOptions::NONE)
                        .decode();
                if decoded.is_invalid()
                    || decoded.len() != instr.len()
                    || decoded.op0_kind() != OpKind::Memory
                    || decoded.memory_base() != Register::None
                    || decoded.memory_index() != instr.memory_index()
                    || decoded.memory_index_scale() != 8
                    || decoded.segment_prefix() != instr.segment_prefix()
                    || (instr.segment_prefix() == Register::DS
                        && encoded.code_buffer.first() != Some(&0x3e))
                    || decoded.memory_displacement64() != targets.tables[&instr.ip()]
                {
                    return Err(format!(
                        "cloned jump at 0x{:x} has an invalid address",
                        instr.ip()
                    )
                    .into());
                }
            }
            code.extend_from_slice(&encoded.code_buffer);
        } else {
            let offset = (instr.ip() - function.start) as usize;
            code.extend_from_slice(&function.bytes[offset..offset + instr.len()]);
        }
        if matches!(
            instr.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) && let Some((route_state, scratch)) = state
        {
            if let Some(slot) = scratch.r10 {
                movq_to_xmm(code, slot, 10);
            }
            if let Some(slot) = scratch.rcx {
                movq_to_xmm(code, slot, 1);
            }
            if let Some(slot) = scratch.r11 {
                movq_to_xmm(code, slot, 11);
                movabs_r11(code, route_state);
                movq_to_xmm(code, scratch.state.unwrap(), 11);
                movq_from_xmm(code, slot, 11);
            } else {
                movabs_r11(code, route_state);
            }
        }
    }
    Ok(())
}

fn write_exit<F>(block: &Block, tail: u64, code: &mut Vec<u8>, mut route: F) -> Result<()>
where
    F: FnMut(u64, usize) -> Result<u64>,
{
    match block.exit {
        Exit::Branch {
            target,
            fallthrough,
            cc,
        } => {
            code.extend_from_slice(&[0x0f, condition_opcode(cc)?]);
            code.extend_from_slice(&rel32(tail + 6, route(target, 0)?)?);
            code.push(0xe9);
            code.extend_from_slice(&rel32(tail + 11, route(fallthrough, 1)?)?);
        }
        Exit::Jump(target) | Exit::Fallthrough(target) => {
            code.push(0xe9);
            code.extend_from_slice(&rel32(tail + 5, route(target, 0)?)?);
        }
        Exit::Return | Exit::Table(_) | Exit::Dispatch(_) => {}
    }
    Ok(())
}

fn encode_direct(
    function: &Function,
    base: u64,
    seed: u64,
    entries: &BTreeMap<u64, u64>,
    table_bases: &BTreeMap<u64, u64>,
    dispatches: &BTreeMap<usize, u64>,
) -> Result<Encoded> {
    let order = permute_all(function.blocks.len(), seed);
    let mut moved = BTreeMap::new();
    let mut cursor = base;
    for &index in &order {
        let block = &function.blocks[index];
        moved.insert(block.old, cursor);
        cursor = cursor
            .checked_add(block.len as u64)
            .ok_or("clone address overflow")?;
    }
    let mut code = Vec::with_capacity((cursor - base) as usize);
    for &index in &order {
        let block = &function.blocks[index];
        write_body(
            function,
            block,
            base,
            &mut code,
            &RewriteTargets {
                moved: &moved,
                entries,
                tables: table_bases,
                references: None,
                calls: None,
            },
            None,
        )?;
        let tail = base + code.len() as u64;
        write_exit(block, tail, &mut code, |target, _| {
            destination(target, function, &moved, entries)
        })?;
        if let Exit::Dispatch(index) = block.exit {
            code.push(0xe9);
            code.extend_from_slice(&rel32(
                tail + 5,
                *dispatches.get(&index).ok_or("missing indexed dispatcher")?,
            )?);
        }
    }
    if code.len() != (cursor - base) as usize {
        return Err("clone length mismatch".into());
    }
    let lengths = function.blocks.iter().map(|b| (b.old, b.len)).collect();
    Ok(Encoded {
        code,
        moved,
        lengths,
    })
}

const PAIRED_BRANCH_TAIL_LEN: usize = 73;
const ROUTE_STUB_LEN: usize = 47;
const RECORD_LEN: usize = 24;
const ROUTE_VARIANTS: usize = 4;
const SELECTOR_LEN: usize = ROUTE_VARIANTS * 256;
const ROUTE_TABLE_LEN: usize = ROUTE_VARIANTS * 4 + 8;
const CALL_STUB_LEN: usize = 34;
const GUARD_LEN: usize = 44;

struct ReferenceSite {
    target: u64,
    key: i32,
    len: usize,
    va: u64,
}

struct CallSite {
    function: usize,
    target: u64,
    key: i32,
    va: u64,
    record: u64,
}

fn call_target(
    site: &CallSite,
    selected: &[Selected],
    entries: &BTreeMap<u64, u64>,
) -> Result<u64> {
    if let Some(&entry) = entries.get(&site.target) {
        return Ok(entry);
    }
    let function = &selected[site.function].function;
    if in_range(site.target, function.start, function.end) {
        return Err("encoded call enters function interior".into());
    }
    Ok(site.target)
}

fn pointer_key(seed: u64, ip: u64) -> i32 {
    ((function_seed(seed ^ 0x082efa98ec4e6c89, ip) & 0x3fff_ffff) + 1) as i32
}

fn encode_pointer(from: u64, target: u64, key: i32) -> u64 {
    (!target.wrapping_sub(from).wrapping_sub(key as u64)).swap_bytes()
}

fn decode_pointer(from: u64, word: u64, key: i32) -> u64 {
    from.wrapping_add(!word.swap_bytes())
        .wrapping_add(key as u64)
}

fn can_encode_reference(instr: &Instruction, function: &Function) -> bool {
    if !instr.is_ip_rel_memory_operand()
        || instr.memory_base() != Register::RIP
        || instr.segment_prefix() != Register::None
        || instr.op0_kind() != OpKind::Register
        || instr.op1_kind() != OpKind::Memory
        || function.tables.iter().any(|table| table.lea == instr.ip())
        || !matches!(
            instr.mnemonic(),
            Mnemonic::Lea | Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd
        )
    {
        return false;
    }
    let register = instr.op0_register();
    if register.size() < 4 || (instr.mnemonic() == Mnemonic::Lea && register.size() != 8) {
        return false;
    }
    matches!(
        register.full_register(),
        Register::RAX
            | Register::RCX
            | Register::RDX
            | Register::RSI
            | Register::RDI
            | Register::R8
            | Register::R9
    )
}

fn gp_number(register: Register) -> Result<u8> {
    Ok(match register {
        Register::RAX => 0,
        Register::RCX => 1,
        Register::RDX => 2,
        Register::RSI => 6,
        Register::RDI => 7,
        Register::R8 => 8,
        Register::R9 => 9,
        _ => return Err("unsupported reference register".into()),
    })
}

fn rip_lea_register(code: &mut Vec<u8>, base: u64, register: Register, target: u64) -> Result<()> {
    let number = register_number(register)?;
    if number == 4 {
        return Err("unsupported table base register".into());
    }
    let address = base + code.len() as u64;
    code.push(0x48 | if number >= 8 { 4 } else { 0 });
    code.push(0x8d);
    code.push(0x05 | ((number & 7) << 3));
    code.extend_from_slice(&rel32(address + 7, target)?);
    Ok(())
}

fn reference_code(instr: &Instruction, address: u64, record: u64, key: i32) -> Result<Vec<u8>> {
    let register = instr.op0_register().full_register();
    let number = gp_number(register)?;
    let high = number >= 8;
    let low = number & 7;
    let mut code = Vec::new();
    code.extend_from_slice(&[0x4c, 0x8d, 0x15]);
    code.extend_from_slice(&rel32(address + 7, record)?);
    code.extend_from_slice(&[0x49 | (u8::from(high) << 2), 0x8b, low << 3 | 2]);
    code.extend_from_slice(&[0x48 | u8::from(high), 0x0f, 0xc8 | low]);
    code.extend_from_slice(&[0x48 | u8::from(high), 0xf7, 0xd0 | low]);
    code.extend_from_slice(&[0x48 | (u8::from(high) * 5), 0x8d, 0x80 | low << 3 | low]);
    code.extend_from_slice(&key.to_le_bytes());
    code.extend_from_slice(&[
        0x49 | (u8::from(high) * 6),
        0x8d,
        low << 3 | 4,
        low << 3 | 2,
    ]);
    if instr.mnemonic() != Mnemonic::Lea {
        let mut load = *instr;
        load.set_memory_base(register);
        load.set_memory_index(Register::None);
        load.set_memory_displacement64(0);
        load.set_memory_displ_size(0);
        let encoded = BlockEncoder::encode(
            64,
            InstructionBlock::new(std::slice::from_ref(&load), address + code.len() as u64),
            BlockEncoderOptions::NONE,
        )
        .map_err(|e| format!("cannot encode reference 0x{:x}: {e}", instr.ip()))?;
        code.extend_from_slice(&encoded.code_buffer);
    }
    Ok(code)
}

fn call_stub(site: &CallSite) -> Result<Vec<u8>> {
    let mut code = ENDBR64.to_vec();
    code.extend_from_slice(&[0x4c, 0x8d, 0x15]);
    code.extend_from_slice(&rel32(site.va + 11, site.record)?);
    code.extend_from_slice(&[0x4d, 0x8b, 0x1a, 0x49, 0x0f, 0xcb, 0x49, 0xf7, 0xd3]);
    code.extend_from_slice(&[0x4d, 0x8d, 0x9b]);
    code.extend_from_slice(&site.key.to_le_bytes());
    code.extend_from_slice(&[0x4f, 0x8d, 0x1c, 0x1a, 0x41, 0xff, 0xe3]);
    if code.len() != CALL_STUB_LEN {
        return Err("call stub length mismatch".into());
    }
    check_handler(&code)?;
    Ok(code)
}

struct StrongFragment {
    function: usize,
    block: Block,
    va: u64,
}

struct RoutePath {
    records: [u64; 2],
    handlers: [usize; 2],
}

struct StrongRoute {
    function: usize,
    scratch: Scratch,
    source: u64,
    arm: usize,
    target: u64,
    paths: [RoutePath; ROUTE_VARIANTS],
    paired: bool,
    indirect: bool,
    guard: Option<usize>,
    va: u64,
    table_va: u64,
}

impl StrongRoute {
    fn stub_len(&self) -> usize {
        ROUTE_STUB_LEN
            + usize::from(self.indirect) * 4
            + self.scratch.route_len()
            + usize::from(self.guard.is_some()) * GUARD_LEN
    }
}

struct PlacedTable {
    function: usize,
    index: usize,
    source: Option<u64>,
    unique: Vec<u64>,
    stubs: Vec<u64>,
    va: u64,
}

struct PlacedDispatch {
    function: usize,
    index: usize,
    source: Option<u64>,
    va: u64,
    table_va: u64,
    arms: Vec<u64>,
}

fn register_number(register: Register) -> Result<u8> {
    match register {
        Register::RAX => Ok(0),
        Register::RCX => Ok(1),
        Register::RDX => Ok(2),
        Register::RBX => Ok(3),
        Register::RSP => Ok(4),
        Register::RBP => Ok(5),
        Register::RSI => Ok(6),
        Register::RDI => Ok(7),
        Register::R8 => Ok(8),
        Register::R9 => Ok(9),
        Register::R10 => Ok(10),
        Register::R11 => Ok(11),
        Register::R12 => Ok(12),
        Register::R13 => Ok(13),
        Register::R14 => Ok(14),
        Register::R15 => Ok(15),
        _ => Err("unsupported dispatch register".into()),
    }
}

fn dispatch_code(table: u64, index: Register, notrack: bool) -> Result<Vec<u8>> {
    let number = register_number(index)?;
    if number == 4 {
        return Err("RSP cannot index a pointer table".into());
    }
    let displacement = i32::try_from(table as i64)
        .ok()
        .filter(|value| *value as i64 as u64 == table)
        .ok_or("cloned pointer table out of range")?;
    let mut code = Vec::with_capacity(9);
    if notrack {
        code.push(0x3e);
    }
    if number >= 8 {
        code.push(0x42);
    }
    code.extend_from_slice(&[0xff, 0x24, 0xc5 | ((number & 7) << 3)]);
    code.extend_from_slice(&displacement.to_le_bytes());
    Ok(code)
}

const DISPATCH_ARM_LEN: usize = 9;

fn dispatch_arm_code(va: u64, target: u64) -> Result<Vec<u8>> {
    let mut code = ENDBR64.to_vec();
    code.push(0xe9);
    code.extend_from_slice(&rel32(va + DISPATCH_ARM_LEN as u64, target)?);
    Ok(code)
}

struct Handler {
    va: u64,
    code: Vec<u8>,
    key1: u64,
    key2: u64,
    variant: usize,
}

impl Handler {
    fn encode(&self, from: u64, target: u64, key: u64) -> u64 {
        let delta = target.wrapping_sub(from);
        if self.variant & 1 == 0 {
            let word = !delta.wrapping_sub(key);
            if self.variant >= 2 {
                word.swap_bytes()
            } else {
                word
            }
        } else {
            let word = !delta;
            (if self.variant >= 2 {
                word.swap_bytes()
            } else {
                word
            })
            .wrapping_sub(key)
        }
    }

    fn decode(&self, from: u64, word: u64, key: u64) -> u64 {
        if self.variant & 1 == 0 {
            let word = if self.variant >= 2 {
                word.swap_bytes()
            } else {
                word
            };
            from.wrapping_add(!word).wrapping_add(key)
        } else {
            let word = word.wrapping_add(key);
            let word = if self.variant >= 2 {
                word.swap_bytes()
            } else {
                word
            };
            from.wrapping_add(!word)
        }
    }
}

#[derive(Clone, Copy)]
enum Part {
    Fragment(usize),
    PairedTail(usize),
    Entry(usize),
    Interior(usize, u64),
    Stub(usize),
    Reference(u64),
    CallStub(u64),
    CallRecord(u64),
    Selector(usize),
    RouteTable(usize),
    Record(usize, usize, usize),
    Handler(usize),
    Layout(usize),
    Table(usize),
    TableStub(usize, usize),
    Dispatch(usize),
    DispatchTable(usize),
    DispatchArm(usize, usize),
}

impl Part {
    fn protected_code(self) -> bool {
        matches!(
            self,
            Self::Fragment(_)
                | Self::Selector(_)
                | Self::Layout(_)
                | Self::PairedTail(_)
                | Self::Entry(_)
                | Self::Interior(_, _)
                | Self::Stub(_)
                | Self::CallStub(_)
                | Self::Handler(_)
                | Self::TableStub(_, _)
                | Self::Dispatch(_)
                | Self::DispatchArm(_, _)
        )
    }
}

fn align_up(value: usize, alignment: usize) -> Result<usize> {
    value
        .checked_add(alignment - 1)
        .map(|v| v & !(alignment - 1))
        .ok_or("clone length overflow".into())
}

fn startup_key(seed: u64) -> u64 {
    function_seed(seed ^ 0x6a09e667f3bcc909, 0x510e527fade682d1)
}

const STARTUP_STEP: u64 = 0x9e3779b97f4a7c15;
const STARTUP_MIX1: u64 = 0xbf58476d1ce4e5b9;
const STARTUP_MIX2: u64 = 0x94d049bb133111eb;

fn mask_startup_code(bytes: &mut [u8], mut state: u64) -> Result<()> {
    if bytes.len() & 7 != 0 {
        return Err("unaligned route region".into());
    }
    for word in bytes.chunks_exact_mut(8) {
        state = state.wrapping_add(STARTUP_STEP);
        let mut mask = state ^ (state >> 30);
        mask = mask.wrapping_mul(STARTUP_MIX1);
        mask ^= mask >> 27;
        mask = mask.wrapping_mul(STARTUP_MIX2);
        mask ^= mask >> 31;
        let value = u64::from_le_bytes(word.try_into().unwrap()) ^ mask;
        word.copy_from_slice(&value.to_le_bytes());
    }
    Ok(())
}

fn patch_local(code: &mut [u8], at: usize, target: usize) -> Result<()> {
    let delta = i32::try_from(target as i64 - (at + 4) as i64)
        .map_err(|_| "decoder branch out of range")?;
    code[at..at + 4].copy_from_slice(&delta.to_le_bytes());
    Ok(())
}

fn startup_decoder(va: u64, code_va: u64, code_len: usize, key: u64) -> Result<Vec<u8>> {
    let len = u32::try_from(code_len).map_err(|_| "protected code exceeds decoder limit")?;
    let words = len / 8;
    let mut code = ENDBR64.to_vec();
    code.push(0x53); // push rbx
    code.extend_from_slice(&[0x48, 0x8d, 0x3d]); // lea rdi, [rip+code]
    let code_ref1 = code.len();
    code.extend_from_slice(&[0; 4]);
    code.push(0xbe);
    code.extend_from_slice(&len.to_le_bytes());
    code.push(0xba);
    code.extend_from_slice(&2u32.to_le_bytes());
    code.push(0xb8);
    code.extend_from_slice(&10u32.to_le_bytes());
    code.extend_from_slice(&[0x0f, 0x05, 0x85, 0xc0, 0x0f, 0x88]);
    let fail1 = code.len();
    code.extend_from_slice(&[0; 4]);
    code.extend_from_slice(&[0x48, 0xbb]);
    code.extend_from_slice(&key.to_le_bytes());
    code.push(0xb9);
    code.extend_from_slice(&words.to_le_bytes());
    for (register, constant) in [
        (0xb8, STARTUP_STEP),
        (0xb9, STARTUP_MIX1),
        (0xba, STARTUP_MIX2),
    ] {
        code.extend_from_slice(&[0x49, register]); // movabs r8/r9/r10, constant
        code.extend_from_slice(&constant.to_le_bytes());
    }
    let loop_at = code.len();
    code.extend_from_slice(&[
        0x4c, 0x01, 0xc3, // add rbx, r8
        0x48, 0x89, 0xd8, // mov rax, rbx
        0x48, 0x89, 0xc2, 0x48, 0xc1, 0xea, 30, 0x48, 0x31, 0xd0, 0x49, 0x0f, 0xaf,
        0xc1, // imul rax, r9
        0x48, 0x89, 0xc2, 0x48, 0xc1, 0xea, 27, 0x48, 0x31, 0xd0, 0x49, 0x0f, 0xaf,
        0xc2, // imul rax, r10
        0x48, 0x89, 0xc2, 0x48, 0xc1, 0xea, 31, 0x48, 0x31, 0xd0, 0x48, 0x31,
        0x07, // xor [rdi], rax
        0x48, 0x83, 0xc7, 0x08, 0xff, 0xc9, 0x0f, 0x85,
    ]);
    let loop_ref = code.len();
    code.extend_from_slice(&[0; 4]);
    code.extend_from_slice(&[0x48, 0x8d, 0x3d]);
    let code_ref2 = code.len();
    code.extend_from_slice(&[0; 4]);
    code.push(0xbe);
    code.extend_from_slice(&len.to_le_bytes());
    code.push(0xba);
    code.extend_from_slice(&5u32.to_le_bytes());
    code.push(0xb8);
    code.extend_from_slice(&10u32.to_le_bytes());
    code.extend_from_slice(&[0x0f, 0x05, 0x85, 0xc0, 0x0f, 0x88]);
    let fail2 = code.len();
    code.extend_from_slice(&[0; 4]);
    code.extend_from_slice(&[0x31, 0xc0, 0x31, 0xc9, 0x0f, 0xa2, 0x5b, 0xc3]);
    let fail_at = code.len();
    code.push(0xb8);
    code.extend_from_slice(&1u32.to_le_bytes());
    code.push(0xbf);
    code.extend_from_slice(&2u32.to_le_bytes());
    code.extend_from_slice(&[0x48, 0x8d, 0x35]);
    let msg_ref = code.len();
    code.extend_from_slice(&[0; 4]);
    let msg = b"elfscatter: code mprotect failed\n";
    code.push(0xba);
    code.extend_from_slice(&(msg.len() as u32).to_le_bytes());
    code.extend_from_slice(&[0x0f, 0x05]);
    code.push(0xb8);
    code.extend_from_slice(&60u32.to_le_bytes());
    code.push(0xbf);
    code.extend_from_slice(&126u32.to_le_bytes());
    code.extend_from_slice(&[0x0f, 0x05, 0x0f, 0x0b]);
    let msg_at = code.len();
    code.extend_from_slice(msg);
    for at in [code_ref1, code_ref2] {
        let target = i128::from(code_va) - i128::from(va + at as u64 + 4);
        let delta = i32::try_from(target).map_err(|_| "decoder code address out of range")?;
        code[at..at + 4].copy_from_slice(&delta.to_le_bytes());
    }
    patch_local(&mut code, fail1, fail_at)?;
    patch_local(&mut code, fail2, fail_at)?;
    patch_local(&mut code, loop_ref, loop_at)?;
    patch_local(&mut code, msg_ref, msg_at)?;
    if code.len() > 4096 {
        return Err("decoder exceeds one page".into());
    }
    Ok(code)
}

fn startup_metadata_capacity(binary: &elf::Binary) -> Result<usize> {
    let dynamic = binary
        .segments()
        .find(|s| s.p_type() == segment::Type::DYNAMIC)
        .ok_or("missing PT_DYNAMIC")?;
    let rela = binary
        .dynamic_entry_by_tag(dynamic::Tag::RELASZ)
        .map_or(0, |e| e.value());
    let preinit = binary
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAYSZ)
        .map_or(0, |e| e.value());
    let total = dynamic
        .physical_size()
        .checked_add(rela)
        .and_then(|v| preinit.checked_mul(4).and_then(|p| v.checked_add(p)))
        .and_then(|v| v.checked_add(4096))
        .ok_or("startup metadata too large")?;
    if total > 256 * 1024 * 1024 {
        return Err("startup metadata exceeds size limit".into());
    }
    align_up(
        usize::try_from(total).map_err(|_| "startup metadata too large")?,
        4096,
    )
}

struct Preinit {
    bytes: Vec<u8>,
    relocations: Vec<(u64, i64)>,
}

fn preinit_input(binary: &elf::Binary) -> Result<Preinit> {
    if binary
        .relocations()
        .any(|r| r.get_type() == relocation::Type::X86_64_IRELATIVE)
        || binary
            .dynamic_symbols()
            .any(|s| s.get_type() == symbol::Type::GNU_IFUNC)
    {
        return Err(Error::Unsupported(
            "startup decoding cannot precede executable IFUNC resolvers".into(),
        ));
    }
    let array = binary
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAY)
        .map(|e| e.value());
    let size = binary
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAYSZ)
        .map(|e| e.value());
    if array.is_some() != size.is_some() {
        return Err("incomplete preinit metadata".into());
    }
    let size = size.unwrap_or(0);
    if size & 7 != 0 || size > 4096 {
        return Err("invalid preinit array size".into());
    }
    let mut result = Preinit {
        bytes: Vec::new(),
        relocations: Vec::new(),
    };
    if size != 0 {
        let base = array.unwrap();
        let end = base
            .checked_add(size)
            .ok_or("preinit array address overflow")?;
        for relocation in binary.relocations() {
            let address = relocation.address();
            let relocation_end = address
                .checked_add(relocation.size().div_ceil(8))
                .ok_or("relocation address overflow")?;
            if address < end
                && relocation_end > base
                && (address < base || (address - base) & 7 != 0 || relocation_end > end)
            {
                return Err("unsupported preinit relocation alignment".into());
            }
        }
        let bytes = binary.content_from_virtual_address(base, size);
        if bytes.len() != size as usize {
            return Err("truncated preinit array".into());
        }
        result.bytes.extend_from_slice(bytes);
        for (i, word) in bytes.chunks_exact(8).enumerate() {
            let slot = base + i as u64 * 8;
            let mut relocations = binary.relocations().filter(|r| r.address() == slot);
            let relocation = relocations.next();
            if relocations.next().is_some() {
                return Err("multiple preinit relocations at one slot".into());
            }
            if let Some(rel) = relocation {
                if rel.get_type() != relocation::Type::X86_64_RELATIVE || !rel.is_rela() {
                    return Err(format!("unsupported preinit relocation at 0x{slot:x}").into());
                }
                result.relocations.push((i as u64 * 8, rel.addend()));
            } else if binary.header().file_type() == header::FileType::DYN && word != [0; 8] {
                return Err(format!("unrelocated PIE preinit callback at 0x{slot:x}").into());
            }
        }
    }
    Ok(result)
}

fn mapped_offset(binary: &elf::Binary, va: u64, size: usize, file_len: usize) -> Result<usize> {
    let mappings = binary
        .segments()
        .filter(|s| s.p_type() == segment::Type::LOAD)
        .map(|s| FileMapping {
            address: s.virtual_address(),
            offset: s.file_offset(),
            size: s.physical_size(),
        });
    Ok(mapped_range(mappings, va, size as u64, file_len)?.start)
}

fn patch_startup_metadata(
    file: &mut [u8],
    data_va: u64,
    capacity: usize,
    decoder_va: u64,
) -> Result<()> {
    let binary = parse_elf(file)?;
    let preinit = preinit_input(&binary)?;
    let pie = binary.header().file_type() == header::FileType::DYN;
    let original = preinit.bytes;
    let mut new_relocations = Vec::new();
    let dynamic_segment = binary
        .segments()
        .find(|s| s.p_type() == segment::Type::DYNAMIC)
        .ok_or("missing PT_DYNAMIC")?;
    let dynamic_phdr_index = binary
        .segments()
        .position(|s| s.p_type() == segment::Type::DYNAMIC)
        .ok_or("missing PT_DYNAMIC")?;
    let dynamic_bytes = dynamic_segment.content();
    let mut tags = Vec::new();
    for row in dynamic_bytes.chunks_exact(16) {
        let tag = u64::from_le_bytes(row[..8].try_into().unwrap());
        if tag == 0 {
            break;
        }
        tags.push((tag, u64::from_le_bytes(row[8..16].try_into().unwrap())));
    }
    if tags.is_empty() {
        return Err("empty PT_DYNAMIC".into());
    }
    let tag_value = |tag: u64| tags.iter().find(|(t, _)| *t == tag).map(|(_, v)| *v);
    let rela_va = tag_value(7).unwrap_or(0);
    let rela_len = tag_value(8).unwrap_or(0);
    if rela_len % 24 != 0 {
        return Err("invalid DT_RELASZ".into());
    }
    if rela_len != 0 && (rela_va == 0 || tag_value(9) != Some(24)) {
        return Err("unsupported dynamic RELA metadata".into());
    }
    let old_rela = if rela_len != 0 {
        let data = binary.content_from_virtual_address(rela_va, rela_len);
        if data.len() != rela_len as usize {
            return Err("truncated dynamic RELA table".into());
        }
        data.to_vec()
    } else {
        Vec::new()
    };
    let dynamic_len = align_up((tags.len() + 6) * 16, 8)?;
    let array_at = dynamic_len;
    let array_len = original
        .len()
        .checked_add(8)
        .ok_or("preinit array too large")?;
    let rela_at = align_up(array_at + array_len, 8)?;
    let array_va = data_va + array_at as u64;
    let new_rela_va = data_va + rela_at as u64;
    let mut array = Vec::with_capacity(array_len);
    array.extend_from_slice(&(if pie { 0 } else { decoder_va }).to_le_bytes());
    array.extend_from_slice(&original);
    if pie {
        new_relocations.push((array_va, decoder_va as i64));
    }
    for (offset, addend) in preinit.relocations {
        new_relocations.push((array_va + 8 + offset, addend));
    }
    let mut rela = old_rela;
    for (slot, addend) in &new_relocations {
        rela.extend_from_slice(&slot.to_le_bytes());
        rela.extend_from_slice(&8u64.to_le_bytes());
        rela.extend_from_slice(&addend.to_le_bytes());
    }
    if rela_at
        .checked_add(rela.len())
        .is_none_or(|end| end > capacity)
    {
        return Err("startup metadata segment too small".into());
    }
    let mut put_tag = |tag: u64, value: u64| {
        if let Some((_, old)) = tags.iter_mut().find(|(t, _)| *t == tag) {
            *old = value;
        } else {
            tags.push((tag, value));
        }
    };
    put_tag(32, array_va);
    put_tag(33, array_len as u64);
    if !rela.is_empty() {
        put_tag(7, new_rela_va);
        put_tag(8, rela.len() as u64);
        put_tag(9, 24);
    }
    let mut data = vec![0u8; capacity];
    for (i, (tag, value)) in tags.iter().enumerate() {
        data[i * 16..i * 16 + 8].copy_from_slice(&tag.to_le_bytes());
        data[i * 16 + 8..i * 16 + 16].copy_from_slice(&value.to_le_bytes());
    }
    data[array_at..array_at + array_len].copy_from_slice(&array);
    data[rela_at..rela_at + rela.len()].copy_from_slice(&rela);
    let data_offset = mapped_offset(&binary, data_va, capacity, file.len())?;
    file[data_offset..data_offset + capacity].copy_from_slice(&data);
    let ph = header_entry(file, false, dynamic_phdr_index)?;
    if u32::from_le_bytes(file[ph..ph + 4].try_into().unwrap()) != 2 {
        return Err("PT_DYNAMIC header changed".into());
    }
    let dyn_size = ((tags.len() + 1) * 16) as u64;
    file[ph + 8..ph + 16].copy_from_slice(&(data_offset as u64).to_le_bytes());
    file[ph + 16..ph + 24].copy_from_slice(&data_va.to_le_bytes());
    file[ph + 24..ph + 32].copy_from_slice(&data_va.to_le_bytes());
    file[ph + 32..ph + 40].copy_from_slice(&dyn_size.to_le_bytes());
    file[ph + 40..ph + 48].copy_from_slice(&dyn_size.to_le_bytes());
    if let Some(index) = binary.sections().position(|s| s.name() == ".dynamic") {
        let sh = header_entry(file, true, index)?;
        file[sh + 16..sh + 24].copy_from_slice(&data_va.to_le_bytes());
        file[sh + 24..sh + 32].copy_from_slice(&(data_offset as u64).to_le_bytes());
        file[sh + 32..sh + 40].copy_from_slice(&dyn_size.to_le_bytes());
    }
    Ok(())
}

fn verify_startup_metadata(
    input: &[u8],
    result: &elf::Binary,
    data_va: u64,
    decoder_va: u64,
    route_va: u64,
    route_len: usize,
    seed: u64,
) -> Result<()> {
    let original = parse_elf(input)?;
    let pie = result.header().file_type() == header::FileType::DYN;
    let old_array = original
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAY)
        .map(|e| e.value());
    let old_size = original
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAYSZ)
        .map_or(0, |e| e.value());
    let new_array = result
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAY)
        .ok_or("rewritten ELF has no preinit array")?
        .value();
    let new_size = result
        .dynamic_entry_by_tag(dynamic::Tag::PREINIT_ARRAYSZ)
        .ok_or("rewritten ELF has no preinit size")?
        .value();
    if new_size != old_size + 8 || new_array < data_va {
        return Err("invalid startup preinit metadata".into());
    }
    let bytes = result.content_from_virtual_address(new_array, new_size);
    if bytes.len() != new_size as usize {
        return Err("truncated startup preinit array".into());
    }
    let original_bytes = if old_size != 0 {
        original.content_from_virtual_address(
            old_array.ok_or("missing original preinit array")?,
            old_size,
        )
    } else {
        &[]
    };
    if bytes[8..] != *original_bytes {
        return Err("existing preinit callbacks changed".into());
    }
    let first = u64::from_le_bytes(bytes[..8].try_into().unwrap());
    if first != if pie { 0 } else { decoder_va } {
        return Err("invalid decoder callback pointer".into());
    }
    if pie {
        let matches: Vec<_> = result
            .relocations()
            .filter(|r| r.address() == new_array)
            .collect();
        if matches.len() != 1
            || matches[0].get_type() != relocation::Type::X86_64_RELATIVE
            || matches[0].addend() != decoder_va as i64
        {
            return Err("missing decoder callback relocation".into());
        }
    }
    for i in 0..(old_size / 8) {
        let old_slot = old_array.unwrap() + i * 8;
        let new_slot = new_array + 8 + i * 8;
        let old: Vec<_> = original
            .relocations()
            .filter(|r| r.address() == old_slot)
            .collect();
        let new: Vec<_> = result
            .relocations()
            .filter(|r| r.address() == new_slot)
            .collect();
        if old.len() != new.len()
            || old
                .iter()
                .zip(new.iter())
                .any(|(a, b)| a.get_type() != b.get_type() || a.addend() != b.addend())
        {
            return Err("existing preinit callback relocations changed".into());
        }
    }
    let old_relocations: Vec<_> = original
        .dynamic_relocations()
        .map(|r| (r.address(), format!("{:?}", r.get_type()), r.addend()))
        .collect();
    let new_relocations: Vec<_> = result
        .dynamic_relocations()
        .map(|r| (r.address(), format!("{:?}", r.get_type()), r.addend()))
        .collect();
    if old_relocations.iter().any(|r| !new_relocations.contains(r)) {
        return Err(Error::Invariant(
            "rewritten ELF lost an original dynamic relocation".into(),
        ));
    }
    let dynamic_va = result
        .segments()
        .find(|s| s.p_type() == segment::Type::DYNAMIC)
        .ok_or("missing PT_DYNAMIC")?
        .virtual_address();
    if dynamic_va < data_va {
        return Err("startup dynamic table is outside metadata segment".into());
    }
    if result.segments().any(|s| {
        s.p_type() == segment::Type::LOAD
            && s.flags() & (segment::Flags::W | segment::Flags::X).bits()
                == (segment::Flags::W | segment::Flags::X).bits()
    }) {
        return Err(Error::Invariant(
            "rewritten ELF has a writable executable segment".into(),
        ));
    }
    if route_va & 4095 != 0 || route_len & 4095 != 0 || decoder_va != route_va + route_len as u64 {
        return Err("invalid startup route page layout".into());
    }
    let decoder = startup_decoder(decoder_va, route_va, route_len, startup_key(seed))?;
    if result.content_from_virtual_address(decoder_va, decoder.len() as u64) != decoder {
        return Err(Error::Invariant(
            "rewritten ELF has an invalid startup decoder".into(),
        ));
    }
    Ok(())
}

fn paired_tail_len(
    block: &Block,
    function: &Function,
    scratch: Scratch,
    guard: bool,
) -> Option<usize> {
    if let Exit::Branch {
        target,
        fallthrough,
        ..
    } = block.exit
        && in_range(target, function.start, function.end)
        && in_range(fallthrough, function.start, function.end)
    {
        Some(PAIRED_BRANCH_TAIL_LEN + scratch.route_len() + usize::from(guard) * GUARD_LEN)
    } else {
        None
    }
}

struct StrongLayout {
    fragments: Vec<StrongFragment>,
    references: BTreeMap<u64, ReferenceSite>,
    calls: BTreeMap<u64, CallSite>,
    routes: Vec<StrongRoute>,
    route_index: BTreeMap<(usize, u64, usize), usize>,
    handlers: Vec<Handler>,
    tables: Vec<PlacedTable>,
    dispatches: Vec<PlacedDispatch>,
    selectors: Vec<u64>,
    entries: Vec<u64>,
    interiors: BTreeMap<u64, u64>,
    layouts: Vec<u64>,
    parts: Vec<Part>,
    order: Vec<usize>,
    capacity: usize,
    base: u64,
    startup_smc: bool,
    paired_tails: Vec<u64>,
    protected_start: usize,
    protected_end: usize,
}

fn next_random(state: &mut u64) -> u64 {
    *state ^= *state >> 12;
    *state ^= *state << 25;
    *state ^= *state >> 27;
    state.wrapping_mul(0x2545f4914f6cdd1d)
}

fn route_state(seed: u64, old: u64, variant: usize) -> u64 {
    ((old ^ function_seed(seed ^ 0x7f4a7c159e3779b9, 0)) << 8) | variant as u64
}

fn entry_stub(va: u64, label: u64, target: u64, scratch: Scratch, seed: u64) -> Result<Vec<u8>> {
    let mut bytes = ENDBR64.to_vec();
    save_route_registers(&mut bytes, scratch);
    movabs_r11(&mut bytes, route_state(seed, label, 0));
    bytes.push(0xe9);
    bytes.extend_from_slice(&rel32(va + bytes.len() as u64 + 4, target)?);
    Ok(bytes)
}

fn route_input(source: u64, seed: u64, scratch: Scratch) -> u8 {
    let mut state = function_seed(seed ^ 0xd1310ba698dfb5ac, source);
    if scratch.rcx.is_some() {
        let registers = [0, 2, 6, 7];
        registers[next_random(&mut state) as usize % registers.len()]
    } else {
        let registers = [0, 1, 2, 6, 7];
        registers[next_random(&mut state) as usize % registers.len()]
    }
}

fn selector_bytes(seed: u64, start: u64) -> Vec<u8> {
    let mut state = function_seed(seed ^ 0xa4093822299f31d0, start);
    let mut bytes = vec![0; SELECTOR_LEN];
    for incoming in 0..ROUTE_VARIANTS {
        let mut values: Vec<u8> = (0..256).map(|byte| (byte % ROUTE_VARIANTS) as u8).collect();
        for index in (1..values.len()).rev() {
            values.swap(index, next_random(&mut state) as usize % (index + 1));
        }
        for (byte, value) in values.into_iter().enumerate() {
            bytes[byte * ROUTE_VARIANTS + incoming] = value;
        }
    }
    bytes
}

fn handler_code(variant: usize, final_step: bool, key1: i32, key2: i32) -> Vec<u8> {
    let mut code = ENDBR64.to_vec();
    code.extend_from_slice(&[0x4d, 0x8b, 0x1a]);
    if variant & 1 == 0 {
        if variant >= 2 {
            code.extend_from_slice(&[0x49, 0x0f, 0xcb]);
        }
        code.extend_from_slice(&[0x49, 0xf7, 0xd3, 0x4f, 0x8d]);
        code.push(if final_step { 0x9c } else { 0x94 });
        code.push(0x1a);
        code.extend_from_slice(&key1.to_le_bytes());
    } else {
        code.extend_from_slice(&[0x4d, 0x8d, 0x9b]);
        code.extend_from_slice(&key1.to_le_bytes());
        if variant >= 2 {
            code.extend_from_slice(&[0x49, 0x0f, 0xcb]);
        }
        code.extend_from_slice(&[0x49, 0xf7, 0xd3, 0x4f, 0x8d]);
        code.push(if final_step { 0x1c } else { 0x14 });
        code.push(0x1a);
    }
    if !final_step {
        code.extend_from_slice(&[0x4d, 0x8b, 0x5a, 0x08]);
        if variant & 1 == 0 {
            if variant >= 2 {
                code.extend_from_slice(&[0x49, 0x0f, 0xcb]);
            }
            code.extend_from_slice(&[0x49, 0xf7, 0xd3, 0x4f, 0x8d, 0x9c, 0x1a]);
            code.extend_from_slice(&key2.to_le_bytes());
        } else {
            code.extend_from_slice(&[0x4d, 0x8d, 0x9b]);
            code.extend_from_slice(&key2.to_le_bytes());
            if variant >= 2 {
                code.extend_from_slice(&[0x49, 0x0f, 0xcb]);
            }
            code.extend_from_slice(&[0x49, 0xf7, 0xd3, 0x4f, 0x8d, 0x1c, 0x1a]);
        }
        code.extend_from_slice(&[0x41, 0xff, 0xe3]);
    } else {
        code.extend_from_slice(&[0x4d, 0x8b, 0x52, 0x10, 0x49, 0xf7, 0xd2]);
        code.extend_from_slice(&[0x4d, 0x8d, 0x92]);
        code.extend_from_slice(&key2.to_le_bytes());
        code.extend_from_slice(&[0x4d, 0x87, 0xda]);
        code.extend_from_slice(&[0x41, 0xff, 0xe2]);
    }
    code
}

fn check_handler(code: &[u8]) -> Result<()> {
    let mut decoder = Decoder::with_ip(64, code, 0, DecoderOptions::NONE);
    let mut ended = false;
    while decoder.can_decode() {
        let instruction = decoder.decode();
        if instruction.is_invalid() || instruction.rflags_modified() != 0 || ended {
            return Err("invalid route handler".into());
        }
        match instruction.flow_control() {
            FlowControl::Next => {}
            FlowControl::IndirectBranch if !decoder.can_decode() => ended = true,
            _ => return Err("invalid route handler".into()),
        }
    }
    if !ended {
        return Err("route handler has no exit".into());
    }
    Ok(())
}

fn check_route_code(code: &[u8], scratch: Scratch) -> Result<()> {
    let mut decoder = Decoder::with_ip(64, code, 0, DecoderOptions::NONE);
    let mut info = InstructionInfoFactory::new();
    let mut ended = false;
    let mut guard_skip = None;
    while decoder.can_decode() {
        let instruction = decoder.decode();
        if instruction.is_invalid() || instruction.rflags_modified() != 0 || ended {
            return Err("invalid route code".into());
        }
        if guard_skip.is_some() && instruction.flow_control() != FlowControl::UnconditionalBranch {
            return Err("invalid route guard".into());
        }
        match instruction.flow_control() {
            FlowControl::Next => {
                for used in info.info(&instruction).used_registers() {
                    let register = used.register().full_register();
                    let allowed = matches!(register, Register::R10 | Register::R11)
                        || (scratch.rcx.is_some() && register == Register::RCX)
                        || xmm_index(used.register()).is_some_and(|index| {
                            [scratch.r10, scratch.r11, scratch.state, scratch.rcx]
                                .contains(&Some(index))
                        });
                    if !allowed
                        && matches!(
                            used.access(),
                            OpAccess::Write
                                | OpAccess::CondWrite
                                | OpAccess::ReadWrite
                                | OpAccess::ReadCondWrite
                        )
                    {
                        return Err("route code writes a source register".into());
                    }
                }
            }
            FlowControl::ConditionalBranch
                if instruction.mnemonic() == Mnemonic::Jrcxz
                    && scratch.rcx.is_some()
                    && guard_skip.is_none() =>
            {
                guard_skip = Some(instruction.near_branch_target());
            }
            FlowControl::UnconditionalBranch
                if guard_skip
                    .take()
                    .is_some_and(|target| target == instruction.next_ip()) => {}
            FlowControl::UnconditionalBranch if !decoder.can_decode() => ended = true,
            _ => return Err("invalid route transfer".into()),
        }
    }
    if !ended {
        return Err("route code has no exit".into());
    }
    Ok(())
}

fn guard_code(va: u64, tag: u64, decoy: u64, source: u64, seed: u64) -> Result<Vec<u8>> {
    let register = [0, 2, 6, 7][function_seed(seed ^ 0x1f83d9abfb41bd6b, source) as usize % 4];
    let mut code = vec![0x45, 0x0f, 0xb6, 0xd3, 0x48, 0x8b, 0xc8 | register];
    code.extend_from_slice(&[0x4a, 0x8d, 0x0c, 0x19, 0x48, 0xf7, 0xd1]);
    code.extend_from_slice(&[0x48, 0x8d, 0x4c, (register << 3) | 1, 1]);
    code.extend_from_slice(&[0x4a, 0x8d, 0x0c, 0x11, 0x49, 0xba]);
    code.extend_from_slice(&tag.to_le_bytes());
    code.extend_from_slice(&[0x4a, 0x8d, 0x0c, 0x11, 0xe3, 5, 0xe9]);
    code.extend_from_slice(&rel32(va + code.len() as u64 + 4, decoy)?);
    if code.len() != GUARD_LEN {
        return Err("route guard length mismatch".into());
    }
    Ok(code)
}

fn add_handler(handlers: &mut Vec<Handler>, state: &mut u64, final_step: bool) -> Result<usize> {
    let kind = next_random(state) as usize % 4;
    let key1 = ((next_random(state) & 0x3fff_ffff) + 1) as i32;
    let key2 = ((next_random(state) & 0x3fff_ffff) + 1) as i32;
    let code = handler_code(kind, final_step, key1, key2);
    check_handler(&code)?;
    let index = handlers.len();
    handlers.push(Handler {
        va: 0,
        code,
        key1: key1 as u64,
        key2: key2 as u64,
        variant: kind,
    });
    Ok(index)
}

impl StrongLayout {
    fn new(
        binary: &elf::Binary,
        selected: &[Selected],
        seed: u64,
        startup_smc: bool,
    ) -> Result<Self> {
        let mut fragments = Vec::new();
        let mut references = BTreeMap::new();
        let mut calls = BTreeMap::new();
        let mut routes = Vec::new();
        let mut handlers = Vec::new();
        let callable: BTreeMap<_, _> = selected
            .iter()
            .flat_map(|item| {
                item.function.entries.iter().map(move |entry| {
                    (
                        entry.label,
                        item.mode() == Mode::Strong
                            || item.function.bytes[(entry.label - item.function.start) as usize..]
                                .starts_with(&ENDBR64),
                    )
                })
            })
            .collect();
        for (index, item) in selected.iter().enumerate() {
            if item.mode() != Mode::Strong {
                continue;
            }
            for mut block in split_fragments(&item.function, seed, item.scratch()) {
                for instr in &block.body {
                    if can_encode_reference(instr, &item.function) {
                        let key = pointer_key(seed, instr.ip());
                        let len = reference_code(instr, 0x1000, 0x2000, key)?.len()
                            + usize::from(item.scratch().r10.is_some()) * 10;
                        block.len = block
                            .len
                            .checked_add(len - instr.len())
                            .ok_or("clone length overflow")?;
                        references.insert(
                            instr.ip(),
                            ReferenceSite {
                                target: instr.ip_rel_memory_address(),
                                key,
                                len,
                                va: 0,
                            },
                        );
                    }
                    if item.scratch().r10.is_none()
                        && item.scratch().r11.is_none()
                        && instr.flow_control() == FlowControl::Call
                        && instr.is_call_near()
                    {
                        let target = instr.near_branch_target();
                        let internal = in_range(target, item.function.start, item.function.end);
                        let safe = (!internal
                            || item
                                .function
                                .entries
                                .iter()
                                .any(|entry| entry.label == target))
                            && callable.get(&target).copied().unwrap_or_else(|| {
                                binary.content_from_virtual_address(target, 4) == ENDBR64
                            });
                        if safe {
                            calls.insert(
                                instr.ip(),
                                CallSite {
                                    function: index,
                                    target,
                                    key: pointer_key(seed, instr.ip()),
                                    va: 0,
                                    record: 0,
                                },
                            );
                        }
                    }
                }
                fragments.push(StrongFragment {
                    function: index,
                    block,
                    va: 0,
                });
            }
        }
        let mut fragment_olds = vec![Vec::new(); selected.len()];
        for fragment in &fragments {
            fragment_olds[fragment.function].push(fragment.block.old);
        }
        let mut opaque_targets = BTreeMap::new();
        for fragment in &mut fragments {
            let function = &selected[fragment.function].function;
            if selected[fragment.function].scratch().rcx.is_none() {
                continue;
            }
            if let Some(target) = alternate_target(
                function,
                &fragment.block,
                &fragment_olds[fragment.function],
                seed,
            ) {
                if matches!(fragment.block.exit,
                    Exit::Branch { target, fallthrough, .. }
                        if in_range(target, function.start, function.end)
                            && in_range(fallthrough, function.start, function.end))
                {
                    fragment.block.len += GUARD_LEN;
                }
                opaque_targets.insert((fragment.function, fragment.block.old), target);
            }
        }
        for fragment in &fragments {
            let function = &selected[fragment.function].function;
            let paired = matches!(fragment.block.exit,
                Exit::Branch { target, fallthrough, .. }
                    if in_range(target, function.start, function.end)
                        && in_range(fallthrough, function.start, function.end));
            let decoy = if let Exit::Branch {
                target,
                fallthrough,
                ..
            } = fragment.block.exit
                && paired
            {
                let candidates: Vec<_> = fragment_olds[fragment.function]
                    .iter()
                    .copied()
                    .filter(|&other| other != target && other != fallthrough)
                    .collect();
                if candidates.is_empty() {
                    None
                } else {
                    let pick = function_seed(seed ^ 0x8ebc6af09c88c6e3, fragment.block.old)
                        as usize
                        % candidates.len();
                    Some(candidates[pick])
                }
            } else {
                None
            };
            let indirect = matches!(fragment.block.exit, Exit::Table(_) | Exit::Dispatch(_));
            let mut targets: Vec<(usize, u64)> = match fragment.block.exit {
                Exit::Branch {
                    target,
                    fallthrough,
                    ..
                } => [Some(target), Some(fallthrough), decoy]
                    .into_iter()
                    .enumerate()
                    .filter_map(|(arm, target)| target.map(|target| (arm, target)))
                    .collect(),
                Exit::Jump(target) | Exit::Fallthrough(target) => vec![(0, target)],
                Exit::Table(index) => function.tables[index]
                    .internal_unique(function)
                    .into_iter()
                    .enumerate()
                    .collect(),
                Exit::Dispatch(index) => function.dispatches[index]
                    .targets
                    .iter()
                    .copied()
                    .filter(|&target| in_range(target, function.start, function.end))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .enumerate()
                    .collect(),
                Exit::Return => Vec::new(),
            };
            if let Some(&target) = opaque_targets.get(&(fragment.function, fragment.block.old)) {
                targets.push((usize::MAX, target));
            }
            if !targets
                .iter()
                .any(|&(_, target)| in_range(target, function.start, function.end))
            {
                continue;
            }
            let mut shared_state = function_seed(seed ^ 0x3c6ef372fe94f82b, fragment.block.old);
            let shared = add_handler(&mut handlers, &mut shared_state, false)?;
            let mut final_handlers = [0; ROUTE_VARIANTS];
            for (variant, slot) in final_handlers.iter_mut().enumerate() {
                let mut state = function_seed(
                    seed ^ fragment.block.old.rotate_left(13),
                    (variant as u64).rotate_left(29),
                );
                *slot = add_handler(&mut handlers, &mut state, true)?;
            }
            for (arm, target) in targets {
                if !in_range(target, function.start, function.end) {
                    continue;
                }
                let paths = std::array::from_fn(|variant| RoutePath {
                    records: [0; 2],
                    handlers: [shared, final_handlers[variant]],
                });
                routes.push(StrongRoute {
                    function: fragment.function,
                    scratch: selected[fragment.function].scratch(),
                    source: fragment.block.old,
                    arm,
                    target,
                    paths,
                    paired: paired && arm != usize::MAX,
                    indirect: indirect && arm != usize::MAX,
                    guard: None,
                    va: 0,
                    table_va: 0,
                });
            }
        }
        let route_index: BTreeMap<_, _> = routes
            .iter()
            .enumerate()
            .map(|(index, route)| ((route.function, route.source, route.arm), index))
            .collect();
        for route in &mut routes {
            if route.arm != usize::MAX {
                route.guard = route_index
                    .get(&(route.function, route.source, usize::MAX))
                    .copied();
            }
        }
        let mut tables = Vec::new();
        for (function_index, item) in selected.iter().enumerate() {
            for (index, table) in item.function.tables.iter().enumerate() {
                let source = if item.mode() == Mode::Strong {
                    Some(
                        fragments
                            .iter()
                            .find(|fragment| {
                                fragment.function == function_index
                                    && matches!(fragment.block.exit, Exit::Table(id) if id == index)
                            })
                            .ok_or("table dispatch fragment missing")?
                            .block
                            .old,
                    )
                } else {
                    None
                };
                let unique = table.internal_unique(&item.function);
                tables.push(PlacedTable {
                    function: function_index,
                    index,
                    source,
                    stubs: vec![0; unique.len()],
                    unique,
                    va: 0,
                });
            }
        }
        let mut dispatches = Vec::new();
        for (function_index, item) in selected.iter().enumerate() {
            for (index, dispatch) in item.function.dispatches.iter().enumerate() {
                let source = if item.mode() == Mode::Strong {
                    Some(
                        fragments
                            .iter()
                            .find(|fragment| {
                                fragment.function == function_index
                                    && matches!(fragment.block.exit, Exit::Dispatch(id) if id == index)
                            })
                            .ok_or("indexed dispatch fragment missing")?
                            .block
                            .old,
                    )
                } else {
                    None
                };
                dispatches.push(PlacedDispatch {
                    function: function_index,
                    index,
                    source,
                    va: 0,
                    table_va: 0,
                    arms: vec![0; dispatch.targets.len()],
                });
            }
        }
        let mut parts = Vec::new();
        for index in 0..fragments.len() {
            parts.push(Part::Fragment(index));
            if startup_smc
                && paired_tail_len(
                    &fragments[index].block,
                    &selected[fragments[index].function].function,
                    selected[fragments[index].function].scratch(),
                    false,
                )
                .is_some()
            {
                parts.push(Part::PairedTail(index));
            }
        }
        for (index, item) in selected.iter().enumerate() {
            if item.mode() == Mode::Strong {
                parts.push(Part::Entry(index));
                for entry in item.function.entries.iter().skip(1) {
                    parts.push(Part::Interior(index, entry.label));
                }
                parts.push(Part::Selector(index));
            }
        }
        for &ip in references.keys() {
            parts.push(Part::Reference(ip));
        }
        for &ip in calls.keys() {
            parts.push(Part::CallStub(ip));
            parts.push(Part::CallRecord(ip));
        }
        for (index, route) in routes.iter().enumerate() {
            if !route.paired {
                parts.push(Part::Stub(index));
            }
            parts.push(Part::RouteTable(index));
            for (variant, path) in route.paths.iter().enumerate() {
                for step in 0..path.records.len() {
                    parts.push(Part::Record(index, variant, step));
                }
            }
        }
        for index in 0..handlers.len() {
            parts.push(Part::Handler(index));
        }
        for (index, item) in selected.iter().enumerate() {
            if item.mode() == Mode::Layout {
                parts.push(Part::Layout(index));
            }
        }
        for (index, table) in tables.iter().enumerate() {
            parts.push(Part::Table(index));
            if selected[table.function].mode() == Mode::Layout {
                for target in 0..table.unique.len() {
                    parts.push(Part::TableStub(index, target));
                }
            }
        }
        for (index, dispatch) in dispatches.iter().enumerate() {
            parts.push(Part::Dispatch(index));
            parts.push(Part::DispatchTable(index));
            for arm in 0..dispatch.arms.len() {
                let function = &selected[dispatch.function].function;
                let target = function.dispatches[dispatch.index].targets[arm];
                if selected[dispatch.function].mode() == Mode::Layout
                    && in_range(target, function.start, function.end)
                {
                    parts.push(Part::DispatchArm(index, arm));
                }
            }
        }
        let startup_smc = startup_smc && parts.iter().any(|part| part.protected_code());
        let order = if startup_smc {
            let clear: Vec<_> = (0..parts.len())
                .filter(|&i| !parts[i].protected_code())
                .collect();
            let protected: Vec<_> = (0..parts.len())
                .filter(|&i| parts[i].protected_code())
                .collect();
            let mut order = Vec::with_capacity(parts.len());
            for i in permute_all(clear.len(), seed ^ 0x243f6a8885a308d3) {
                order.push(clear[i]);
            }
            for i in permute_all(protected.len(), seed ^ 0x13198a2e03707344) {
                order.push(protected[i]);
            }
            order
        } else {
            permute_all(parts.len(), seed ^ 0x243f6a8885a308d3)
        };
        let fragment_count = fragments.len();
        let mut layout = Self {
            fragments,
            references,
            calls,
            routes,
            route_index,
            handlers,
            tables,
            dispatches,
            selectors: vec![0; selected.len()],
            entries: vec![0; selected.len()],
            interiors: BTreeMap::new(),
            layouts: vec![0; selected.len()],
            order,
            parts,
            capacity: 0,
            base: 0,
            startup_smc,
            paired_tails: vec![0; fragment_count],
            protected_start: 0,
            protected_end: 0,
        };
        let mut protected_started = false;
        for &i in &layout.order {
            if startup_smc && layout.parts[i].protected_code() && !protected_started {
                protected_started = true;
                layout.capacity = align_up(layout.capacity, 4096)?;
                layout.protected_start = layout.capacity;
            }
            layout.capacity = layout
                .capacity
                .checked_add(layout.part_len(layout.parts[i], selected)?)
                .ok_or("clone length overflow")?;
        }
        if startup_smc {
            layout.capacity = align_up(layout.capacity, 4096)?;
            layout.protected_end = layout.capacity;
        }
        Ok(layout)
    }

    fn part_len(&self, part: Part, selected: &[Selected]) -> Result<usize> {
        Ok(match part {
            Part::Fragment(index) => {
                let item = &self.fragments[index];
                let mut len = item.block.len;
                if self.startup_smc {
                    let guard = self
                        .route_index
                        .get(&(item.function, item.block.old, 0))
                        .is_some_and(|&i| self.routes[i].guard.is_some());
                    if let Some(tail) = paired_tail_len(
                        &item.block,
                        &selected[item.function].function,
                        selected[item.function].scratch(),
                        guard,
                    ) {
                        len = len
                            .checked_sub(tail)
                            .ok_or("paired tail length exceeds fragment")?
                            + 5;
                    }
                }
                len + usize::from(fragment_endbr(
                    &selected[item.function].function,
                    &item.block,
                    selected[item.function].scratch(),
                )) * 4
                    + selected[item.function].scratch().prefix_len()
            }
            Part::PairedTail(index) => {
                let item = &self.fragments[index];
                let guard = self
                    .route_index
                    .get(&(item.function, item.block.old, 0))
                    .is_some_and(|&i| self.routes[i].guard.is_some());
                paired_tail_len(
                    &item.block,
                    &selected[item.function].function,
                    selected[item.function].scratch(),
                    guard,
                )
                .ok_or("missing paired tail")?
            }
            Part::Entry(index) => selected[index].scratch().entry_len(),
            Part::Interior(index, _) => selected[index].scratch().entry_len(),
            Part::Stub(index) => self.routes[index].stub_len(),
            Part::Reference(_) | Part::CallRecord(_) => 8,
            Part::CallStub(_) => CALL_STUB_LEN,
            Part::Selector(_) => SELECTOR_LEN,
            Part::RouteTable(_) => ROUTE_TABLE_LEN,
            Part::Record(_, _, _) => RECORD_LEN,
            Part::Handler(index) => self.handlers[index].code.len(),
            Part::Layout(index) => encoded_capacity(&selected[index].function)?,
            Part::Table(index) => {
                let table = &self.tables[index];
                selected[table.function].function.tables[table.index]
                    .targets
                    .len()
                    .checked_mul(selected[table.function].function.tables[table.index].width())
                    .ok_or("table length overflow")?
            }
            Part::TableStub(_, _) => 9,
            Part::Dispatch(index) => {
                let placed = &self.dispatches[index];
                let dispatch = &selected[placed.function].function.dispatches[placed.index];
                dispatch_code(0, dispatch.index, dispatch.notrack)?.len()
            }
            Part::DispatchTable(index) => self.dispatches[index]
                .arms
                .len()
                .checked_mul(8)
                .ok_or("dispatch table length overflow")?,
            Part::DispatchArm(_, _) => DISPATCH_ARM_LEN,
        })
    }

    fn place(&mut self, base: u64, selected: &[Selected]) -> Result<()> {
        if base & 255 != 0 {
            return Err("clone base is not aligned for route state".into());
        }
        self.base = base;
        let mut cursor = base;
        for &part_index in &self.order {
            let part = self.parts[part_index];
            if self.startup_smc
                && part.protected_code()
                && cursor < base + self.protected_start as u64
            {
                cursor = base + self.protected_start as u64;
            }
            match part {
                Part::Fragment(index) => self.fragments[index].va = cursor,
                Part::PairedTail(index) => self.paired_tails[index] = cursor,
                Part::Entry(index) => self.entries[index] = cursor,
                Part::Interior(_, label) => {
                    self.interiors.insert(label, cursor);
                }
                Part::Stub(index) => self.routes[index].va = cursor,
                Part::Reference(ip) => self.references.get_mut(&ip).unwrap().va = cursor,
                Part::CallStub(ip) => self.calls.get_mut(&ip).unwrap().va = cursor,
                Part::CallRecord(ip) => self.calls.get_mut(&ip).unwrap().record = cursor,
                Part::Selector(index) => self.selectors[index] = cursor,
                Part::RouteTable(index) => self.routes[index].table_va = cursor,
                Part::Record(index, variant, step) => {
                    self.routes[index].paths[variant].records[step] = cursor;
                }
                Part::Handler(index) => self.handlers[index].va = cursor,
                Part::Layout(index) => self.layouts[index] = cursor,
                Part::Table(index) => self.tables[index].va = cursor,
                Part::TableStub(index, target) => self.tables[index].stubs[target] = cursor,
                Part::Dispatch(index) => self.dispatches[index].va = cursor,
                Part::DispatchTable(index) => self.dispatches[index].table_va = cursor,
                Part::DispatchArm(index, arm) => self.dispatches[index].arms[arm] = cursor,
            }
            cursor = cursor
                .checked_add(self.part_len(part, selected)? as u64)
                .ok_or("clone address overflow")?;
        }
        if self.startup_smc {
            cursor = base + self.capacity as u64;
        }
        if cursor - base != self.capacity as u64 {
            return Err("clone length mismatch".into());
        }
        Ok(())
    }
}

struct CodeImage {
    code: Vec<u8>,
    moved: BTreeMap<u64, u64>,
    lengths: BTreeMap<u64, usize>,
    entries: BTreeMap<u64, u64>,
}

fn put(code: &mut [u8], base: u64, va: u64, bytes: &[u8], expected: usize) -> Result<()> {
    if bytes.len() != expected {
        return Err("clone length mismatch".into());
    }
    let offset = usize::try_from(va.checked_sub(base).ok_or("clone address underflow")?)
        .map_err(|_| "clone address overflow")?;
    let slot = code
        .get_mut(offset..offset + expected)
        .ok_or("clone address outside segment")?;
    slot.copy_from_slice(bytes);
    Ok(())
}

fn movq_to_xmm(code: &mut Vec<u8>, xmm: u8, gp: u8) {
    code.extend_from_slice(&[
        0x66,
        0x4c | u8::from(gp >= 8),
        0x0f,
        0x6e,
        0xc0 | ((xmm & 7) << 3) | (gp & 7),
    ]);
}

fn movq_from_xmm(code: &mut Vec<u8>, xmm: u8, gp: u8) {
    code.extend_from_slice(&[
        0x66,
        0x4c | u8::from(gp >= 8),
        0x0f,
        0x7e,
        0xc0 | ((xmm & 7) << 3) | (gp & 7),
    ]);
}

fn save_route_registers(code: &mut Vec<u8>, scratch: Scratch) {
    if let Some(slot) = scratch.r10 {
        movq_to_xmm(code, slot, 10);
    }
    if let Some(slot) = scratch.r11 {
        movq_to_xmm(code, slot, 11);
    }
    if let Some(slot) = scratch.rcx {
        movq_to_xmm(code, slot, 1);
    }
}

fn fragment_prefix(code: &mut Vec<u8>, scratch: Scratch) {
    if let Some(slot) = scratch.state {
        movq_to_xmm(code, slot, 11);
    }
    if let Some(slot) = scratch.r10 {
        movq_from_xmm(code, slot, 10);
    }
    if let Some(slot) = scratch.r11 {
        movq_from_xmm(code, slot, 11);
    }
    if let Some(slot) = scratch.rcx {
        movq_from_xmm(code, slot, 1);
    }
}

fn route_prefix(code: &mut Vec<u8>, scratch: Scratch) {
    save_route_registers(code, scratch);
    if let Some(slot) = scratch.state {
        movq_from_xmm(code, slot, 11);
    }
}

fn rip_lea_r11(code: &mut Vec<u8>, va: u64, target: u64) -> Result<()> {
    code.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
    code.extend_from_slice(&rel32(va + code.len() as u64 + 4, target)?);
    Ok(())
}

fn movabs_r11(code: &mut Vec<u8>, state: u64) {
    code.extend_from_slice(&[0x49, 0xbb]);
    code.extend_from_slice(&state.to_le_bytes());
}

fn rip_cmov_r10(code: &mut Vec<u8>, va: u64, cc: u8, pointer: u64) -> Result<()> {
    code.extend_from_slice(&[0x4c, 0x0f, cc - 0x40, 0x15]);
    code.extend_from_slice(&rel32(va + code.len() as u64 + 4, pointer)?);
    Ok(())
}

fn route_selector(code: &mut Vec<u8>, va: u64, selector: u64, register: u8) -> Result<()> {
    code.extend_from_slice(&[0x44, 0x0f, 0xb6, 0xd0 | register]);
    code.extend_from_slice(&[0x45, 0x0f, 0xb6, 0xdb]);
    code.extend_from_slice(&[0x4f, 0x8d, 0x14, 0x93]);
    rip_lea_r11(code, va, selector)?;
    code.extend_from_slice(&[0x47, 0x0f, 0xb6, 0x14, 0x13]);
    Ok(())
}

fn route_transfer(code: &mut Vec<u8>, va: u64, handler: u64) -> Result<()> {
    code.extend_from_slice(&[0x4d, 0x63, 0x13]);
    code.extend_from_slice(&[0x4f, 0x8d, 0x14, 0x13]);
    code.push(0xe9);
    code.extend_from_slice(&rel32(va + code.len() as u64 + 4, handler)?);
    Ok(())
}

fn route_stub(
    route: &StrongRoute,
    handlers: &[Handler],
    selector: u64,
    decoy: Option<u64>,
    seed: u64,
) -> Result<Vec<u8>> {
    let mut code = Vec::with_capacity(route.stub_len());
    if route.indirect {
        code.extend_from_slice(&ENDBR64);
    }
    route_prefix(&mut code, route.scratch);
    if let Some(decoy) = decoy {
        code.extend_from_slice(&guard_code(
            route.va + code.len() as u64,
            route_state(seed, route.source, 0),
            decoy,
            route.source,
            seed,
        )?);
    }
    route_selector(
        &mut code,
        route.va,
        selector,
        route_input(route.source, seed, route.scratch),
    )?;
    rip_lea_r11(&mut code, route.va, route.table_va)?;
    code.extend_from_slice(&[0x4f, 0x8d, 0x1c, 0x93]);
    route_transfer(&mut code, route.va, handlers[route.paths[0].handlers[0]].va)?;
    if code.len() != route.stub_len() {
        return Err("route stub length mismatch".into());
    }
    check_route_code(&code, route.scratch)?;
    Ok(code)
}

fn route_record(
    route: &StrongRoute,
    variant: usize,
    step: usize,
    handlers: &[Handler],
    moved: &BTreeMap<u64, u64>,
    seed: u64,
) -> Result<[u8; RECORD_LEN]> {
    let path = &route.paths[variant];
    let va = path.records[step];
    let handler = &handlers[path.handlers[step]];
    let next = if step + 1 == path.records.len() {
        *moved
            .get(&route.target)
            .ok_or_else(|| format!("unmapped edge target 0x{:x}", route.target))?
    } else {
        path.records[step + 1]
    };
    let first = handler.encode(va, next, handler.key1);
    let second = if step == 0 {
        function_seed(seed, route.source ^ route.target)
    } else {
        let previous = &handlers[path.handlers[step - 1]];
        previous.encode(va, handler.va, previous.key2)
    };
    let mut bytes = [0; RECORD_LEN];
    bytes[..8].copy_from_slice(&first.to_le_bytes());
    bytes[8..16].copy_from_slice(&second.to_le_bytes());
    let third = if step + 1 == path.records.len() {
        !route_state(seed, route.target, variant).wrapping_sub(handler.key2)
    } else {
        function_seed(seed ^ 0x9e3779b97f4a7c15, va)
    };
    bytes[16..24].copy_from_slice(&third.to_le_bytes());
    Ok(bytes)
}

impl StrongLayout {
    fn decoy_route<'a>(&'a self, route: &'a StrongRoute) -> &'a StrongRoute {
        self.route_index
            .get(&(route.function, route.source, 2))
            .or_else(|| self.route_index.get(&(route.function, route.source, 1)))
            .map(|&index| &self.routes[index])
            .unwrap_or(route)
    }

    fn paired_tail(
        &self,
        fragment: &StrongFragment,
        scratch: Scratch,
        va: u64,
        seed: u64,
    ) -> Result<Vec<u8>> {
        let Exit::Branch { cc, .. } = fragment.block.exit else {
            return Err("missing paired branch".into());
        };
        let true_route = &self.routes[*self
            .route_index
            .get(&(fragment.function, fragment.block.old, 0))
            .ok_or("missing true route")?];
        let false_route = &self.routes[*self
            .route_index
            .get(&(fragment.function, fragment.block.old, 1))
            .ok_or("missing false route")?];
        let decoy_route = self.decoy_route(false_route);
        if true_route.paths[0].handlers[0] != false_route.paths[0].handlers[0]
            || true_route.paths[0].handlers[0] != decoy_route.paths[0].handlers[0]
        {
            return Err("branch routes have different handlers".into());
        }
        let mut bytes = Vec::new();
        route_prefix(&mut bytes, scratch);
        if let Some(decoy) = true_route.guard {
            bytes.extend_from_slice(&guard_code(
                va + bytes.len() as u64,
                route_state(seed, fragment.block.old, 0),
                self.routes[decoy].va,
                fragment.block.old,
                seed,
            )?);
        }
        route_selector(
            &mut bytes,
            va,
            self.selectors[fragment.function],
            route_input(fragment.block.old, seed, scratch),
        )?;
        rip_lea_r11(&mut bytes, va, decoy_route.table_va)?;
        bytes.extend_from_slice(&[0x4f, 0x8d, 0x1c, 0x93]);
        bytes.extend_from_slice(&[0x41, 0xba, 0, 0, 0, 0]);
        let condition = condition_opcode(cc)?;
        rip_cmov_r10(&mut bytes, va, condition, true_route.table_va + 16)?;
        rip_cmov_r10(&mut bytes, va, condition ^ 1, false_route.table_va + 16)?;
        bytes.extend_from_slice(&[0x4f, 0x8d, 0x1c, 0x13]);
        route_transfer(
            &mut bytes,
            va,
            self.handlers[true_route.paths[0].handlers[0]].va,
        )?;
        check_route_code(&bytes, scratch)?;
        Ok(bytes)
    }

    fn encode(&self, selected: &[Selected], seed: u64) -> Result<CodeImage> {
        let mut moved = BTreeMap::new();
        let mut lengths = BTreeMap::new();
        for (index, fragment) in self.fragments.iter().enumerate() {
            moved.insert(fragment.block.old, fragment.va);
            lengths.insert(
                fragment.block.old,
                self.part_len(Part::Fragment(index), selected)?,
            );
        }
        let mut entries = BTreeMap::new();
        for (index, item) in selected.iter().enumerate() {
            if item.mode() == Mode::Vm {
                continue;
            }
            for entry in &item.function.entries {
                let va = if item.mode() == Mode::Strong {
                    if entry.label == item.function.start {
                        self.entries[index]
                    } else {
                        self.interiors[&entry.label]
                    }
                } else {
                    self.layouts[index]
                        .checked_add(entry_offset(
                            &item.function,
                            function_seed(seed, item.function.start),
                            entry.label,
                        )? as u64)
                        .ok_or("clone address overflow")?
                };
                entries.insert(entry.label, va);
            }
        }
        let route_addresses: BTreeMap<_, _> = self
            .routes
            .iter()
            .map(|route| ((route.function, route.source, route.arm), route.va))
            .collect();
        let mut table_bases = vec![BTreeMap::new(); selected.len()];
        let mut dispatch_addresses = vec![BTreeMap::new(); selected.len()];
        for table in &self.tables {
            let source = &selected[table.function].function.tables[table.index];
            table_bases[table.function].insert(
                source.setup.map_or(source.lea, |setup| setup.load),
                table.va,
            );
        }
        for dispatch in &self.dispatches {
            dispatch_addresses[dispatch.function].insert(dispatch.index, dispatch.va);
        }
        let mut code = vec![0xcc; self.capacity];
        for part in &self.parts {
            match *part {
                Part::Fragment(index) => {
                    let fragment = &self.fragments[index];
                    let function = &selected[fragment.function].function;
                    let mut bytes = Vec::with_capacity(lengths[&fragment.block.old]);
                    if fragment_endbr(
                        function,
                        &fragment.block,
                        selected[fragment.function].scratch(),
                    ) {
                        bytes.extend_from_slice(&ENDBR64);
                    }
                    let scratch = selected[fragment.function].scratch();
                    fragment_prefix(&mut bytes, scratch);
                    write_body(
                        function,
                        &fragment.block,
                        fragment.va,
                        &mut bytes,
                        &RewriteTargets {
                            moved: &moved,
                            entries: &entries,
                            tables: &table_bases[fragment.function],
                            references: Some(&self.references),
                            calls: Some(&self.calls),
                        },
                        Some((route_state(seed, fragment.block.old, 0), scratch)),
                    )?;
                    let tail = fragment.va + bytes.len() as u64;
                    if let Exit::Branch {
                        target,
                        fallthrough,
                        cc: _,
                    } = fragment.block.exit
                        && in_range(target, function.start, function.end)
                        && in_range(fallthrough, function.start, function.end)
                    {
                        if self.startup_smc {
                            bytes.push(0xe9);
                            bytes.extend_from_slice(&rel32(tail + 5, self.paired_tails[index])?);
                        } else {
                            let route = self.paired_tail(fragment, scratch, tail, seed)?;
                            bytes.extend_from_slice(&route);
                        }
                        if bytes.len() != lengths[&fragment.block.old] {
                            return Err("branch route length mismatch".into());
                        }
                    } else {
                        write_exit(&fragment.block, tail, &mut bytes, |target, arm| {
                            if in_range(target, function.start, function.end) {
                                route_addresses
                                    .get(&(fragment.function, fragment.block.old, arm))
                                    .copied()
                                    .ok_or_else(|| {
                                        Error::Invariant(format!(
                                            "missing route at 0x{:x}",
                                            fragment.block.old
                                        ))
                                    })
                            } else {
                                Ok(entries.get(&target).copied().unwrap_or(target))
                            }
                        })?;
                        if let Exit::Dispatch(index) = fragment.block.exit {
                            bytes.push(0xe9);
                            bytes.extend_from_slice(&rel32(
                                tail + 5,
                                dispatch_addresses[fragment.function][&index],
                            )?);
                        }
                    }
                    put(
                        &mut code,
                        self.base,
                        fragment.va,
                        &bytes,
                        lengths[&fragment.block.old],
                    )?;
                }
                Part::PairedTail(index) => {
                    let fragment = &self.fragments[index];
                    let va = self.paired_tails[index];
                    let bytes = self.paired_tail(
                        fragment,
                        selected[fragment.function].scratch(),
                        va,
                        seed,
                    )?;
                    put(
                        &mut code,
                        self.base,
                        va,
                        &bytes,
                        self.part_len(*part, selected)?,
                    )?;
                }
                Part::Entry(index) => {
                    let entry = self.entries[index];
                    let start = selected[index].function.start;
                    let target = *moved.get(&start).ok_or("entry fragment missing")?;
                    let bytes = entry_stub(entry, start, target, selected[index].scratch(), seed)?;
                    put(
                        &mut code,
                        self.base,
                        entry,
                        &bytes,
                        selected[index].scratch().entry_len(),
                    )?;
                }
                Part::Interior(index, label) => {
                    let va = self.interiors[&label];
                    let target = *moved.get(&label).ok_or("interior fragment missing")?;
                    let bytes = entry_stub(va, label, target, selected[index].scratch(), seed)?;
                    put(
                        &mut code,
                        self.base,
                        va,
                        &bytes,
                        selected[index].scratch().entry_len(),
                    )?;
                }
                Part::Stub(index) => {
                    let route = &self.routes[index];
                    put(
                        &mut code,
                        self.base,
                        route.va,
                        &route_stub(
                            route,
                            &self.handlers,
                            self.selectors[route.function],
                            route.guard.map(|index| self.routes[index].va),
                            seed,
                        )?,
                        route.stub_len(),
                    )?;
                }
                Part::Reference(ip) => {
                    let site = &self.references[&ip];
                    let word = encode_pointer(site.va, site.target, site.key);
                    put(&mut code, self.base, site.va, &word.to_le_bytes(), 8)?;
                }
                Part::CallStub(ip) => {
                    let site = &self.calls[&ip];
                    let bytes = call_stub(site)?;
                    put(&mut code, self.base, site.va, &bytes, CALL_STUB_LEN)?;
                }
                Part::CallRecord(ip) => {
                    let site = &self.calls[&ip];
                    let target = call_target(site, selected, &entries)?;
                    let word = encode_pointer(site.record, target, site.key);
                    put(&mut code, self.base, site.record, &word.to_le_bytes(), 8)?;
                }
                Part::Selector(index) => {
                    let bytes = selector_bytes(seed, selected[index].function.start);
                    put(
                        &mut code,
                        self.base,
                        self.selectors[index],
                        &bytes,
                        SELECTOR_LEN,
                    )?;
                }
                Part::RouteTable(index) => {
                    let route = &self.routes[index];
                    let mut bytes = Vec::with_capacity(ROUTE_TABLE_LEN);
                    for (variant, path) in route.paths.iter().enumerate() {
                        bytes.extend_from_slice(&rel32(
                            route.table_va + (variant * 4) as u64,
                            path.records[0],
                        )?);
                    }
                    let decoy = self.decoy_route(route);
                    bytes.extend_from_slice(
                        &route.table_va.wrapping_sub(decoy.table_va).to_le_bytes(),
                    );
                    put(
                        &mut code,
                        self.base,
                        route.table_va,
                        &bytes,
                        ROUTE_TABLE_LEN,
                    )?;
                }
                Part::Record(index, variant, step) => {
                    let route = &self.routes[index];
                    let va = route.paths[variant].records[step];
                    let bytes = route_record(route, variant, step, &self.handlers, &moved, seed)?;
                    put(&mut code, self.base, va, &bytes, RECORD_LEN)?;
                }
                Part::Handler(index) => {
                    let handler = &self.handlers[index];
                    put(
                        &mut code,
                        self.base,
                        handler.va,
                        &handler.code,
                        handler.code.len(),
                    )?;
                }
                Part::Layout(index) => {
                    let function = &selected[index].function;
                    let encoded = encode_direct(
                        function,
                        self.layouts[index],
                        function_seed(seed, function.start),
                        &entries,
                        &table_bases[index],
                        &dispatch_addresses[index],
                    )?;
                    if encoded.moved[&function.start] != entries[&function.start] {
                        return Err("entry layout mismatch".into());
                    }
                    put(
                        &mut code,
                        self.base,
                        self.layouts[index],
                        &encoded.code,
                        self.part_len(*part, selected)?,
                    )?;
                    moved.extend(encoded.moved);
                    lengths.extend(encoded.lengths);
                }
                Part::Dispatch(index) => {
                    let placed = &self.dispatches[index];
                    let source = &selected[placed.function].function.dispatches[placed.index];
                    let bytes = dispatch_code(placed.table_va, source.index, source.notrack)?;
                    put(
                        &mut code,
                        self.base,
                        placed.va,
                        &bytes,
                        self.part_len(*part, selected)?,
                    )?;
                }
                Part::Table(_)
                | Part::TableStub(_, _)
                | Part::DispatchTable(_)
                | Part::DispatchArm(_, _) => {}
            }
        }
        for placed in &self.dispatches {
            let function = &selected[placed.function].function;
            let source = &function.dispatches[placed.index];
            let mut table = Vec::with_capacity(source.targets.len() * 8);
            let internal: Vec<_> = source
                .targets
                .iter()
                .copied()
                .filter(|&target| in_range(target, function.start, function.end))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            for (arm, &va) in placed.arms.iter().enumerate() {
                let target = source.targets[arm];
                let routed = if in_range(target, function.start, function.end) {
                    if selected[placed.function].mode() == Mode::Strong {
                        let route_arm = internal
                            .binary_search(&target)
                            .map_err(|_| "dispatch route target missing")?;
                        *route_addresses
                            .get(&(
                                placed.function,
                                placed.source.ok_or("dispatch route source missing")?,
                                route_arm,
                            ))
                            .ok_or("dispatch route missing")?
                    } else {
                        let bytes = dispatch_arm_code(
                            va,
                            *moved.get(&target).ok_or("dispatch target missing")?,
                        )?;
                        put(&mut code, self.base, va, &bytes, DISPATCH_ARM_LEN)?;
                        va
                    }
                } else {
                    target
                };
                table.extend_from_slice(&routed.to_le_bytes());
            }
            put(&mut code, self.base, placed.table_va, &table, table.len())?;
        }
        for table in &self.tables {
            let source = &selected[table.function].function.tables[table.index];
            let function = &selected[table.function].function;
            let mut bytes = Vec::with_capacity(source.targets.len() * source.width());
            for &target in &source.targets {
                if !in_range(target, function.start, function.end) {
                    if source.kind != TableKind::Absolute {
                        return Err("relative table has an external target".into());
                    }
                    bytes.extend_from_slice(&target.to_le_bytes());
                    continue;
                }
                let arm = table
                    .unique
                    .binary_search(&target)
                    .map_err(|_| "table target missing")?;
                let stub = if selected[table.function].mode() == Mode::Strong {
                    *route_addresses
                        .get(&(
                            table.function,
                            table.source.ok_or("table route source missing")?,
                            arm,
                        ))
                        .ok_or("table route missing")?
                } else {
                    table.stubs[arm]
                };
                if source.kind == TableKind::Absolute {
                    bytes.extend_from_slice(&stub.to_le_bytes());
                } else {
                    let delta = stub as i128 - table.va as i128;
                    bytes.extend_from_slice(
                        &i32::try_from(delta)
                            .map_err(|_| "table target out of range")?
                            .to_le_bytes(),
                    );
                }
            }
            put(&mut code, self.base, table.va, &bytes, bytes.len())?;
            if selected[table.function].mode() == Mode::Layout {
                for (arm, &target) in table.unique.iter().enumerate() {
                    let va = table.stubs[arm];
                    let mut stub = ENDBR64.to_vec();
                    stub.push(0xe9);
                    stub.extend_from_slice(&rel32(va + 9, moved[&target])?);
                    put(&mut code, self.base, va, &stub, 9)?;
                }
            }
        }
        Ok(CodeImage {
            code,
            moved,
            lengths,
            entries,
        })
    }

    fn verify_routes(
        &self,
        result: &elf::Binary,
        selected: &[Selected],
        moved: &BTreeMap<u64, u64>,
        lengths: &BTreeMap<u64, usize>,
        entries: &BTreeMap<u64, u64>,
        seed: u64,
    ) -> Result<()> {
        for handler in &self.handlers {
            if result.content_from_virtual_address(handler.va, 4) != ENDBR64 {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid handler".into(),
                ));
            }
        }
        for (index, item) in selected
            .iter()
            .enumerate()
            .filter(|(_, item)| item.mode() == Mode::Strong)
        {
            let expected = selector_bytes(seed, item.function.start);
            if result.content_from_virtual_address(self.selectors[index], SELECTOR_LEN as u64)
                != expected
            {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid route selector".into(),
                ));
            }
        }
        for site in self.references.values() {
            let data = result.content_from_virtual_address(site.va, 8);
            let word = u64::from_le_bytes(
                data.try_into()
                    .map_err(|_| "rewritten ELF has a truncated reference record")?,
            );
            if decode_pointer(site.va, word, site.key) != site.target {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid reference record".into(),
                ));
            }
        }
        for site in self.calls.values() {
            let target = call_target(site, selected, entries)?;
            let data = result.content_from_virtual_address(site.record, 8);
            let word = u64::from_le_bytes(
                data.try_into()
                    .map_err(|_| "rewritten ELF has a truncated call record")?,
            );
            if decode_pointer(site.record, word, site.key) != target
                || result.content_from_virtual_address(site.va, CALL_STUB_LEN as u64)
                    != call_stub(site)?
                || result.content_from_virtual_address(target, 4) != ENDBR64
            {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid call route".into(),
                ));
            }
        }
        for route in &self.routes {
            if route.indirect && result.content_from_virtual_address(route.va, 4) != ENDBR64 {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid table route stub".into(),
                ));
            }
            let target = moved[&route.target];
            if result.content_from_virtual_address(target, 4) != ENDBR64 {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid indirect target".into(),
                ));
            }
            let table = result.content_from_virtual_address(route.table_va, ROUTE_TABLE_LEN as u64);
            let decoy = self.decoy_route(route);
            if table.len() != ROUTE_TABLE_LEN
                || u64::from_le_bytes(table[16..24].try_into().unwrap())
                    != route.table_va.wrapping_sub(decoy.table_va)
            {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid route table".into(),
                ));
            }
            for (variant, path) in route.paths.iter().enumerate() {
                let offset = variant * 4;
                let delta = i32::from_le_bytes(table[offset..offset + 4].try_into().unwrap());
                if u64::try_from(route.table_va as i128 + offset as i128 + delta as i128).ok()
                    != Some(path.records[0])
                {
                    return Err(Error::Invariant(
                        "rewritten ELF has an invalid route table entry".into(),
                    ));
                }
                for (step, &va) in path.records.iter().enumerate() {
                    let data = result.content_from_virtual_address(va, RECORD_LEN as u64);
                    let bytes: [u8; RECORD_LEN] = data
                        .try_into()
                        .map_err(|_| "rewritten ELF has a truncated route record")?;
                    let first = u64::from_le_bytes(bytes[..8].try_into().unwrap());
                    let handler = &self.handlers[path.handlers[step]];
                    let next = if step + 1 == path.records.len() {
                        target
                    } else {
                        path.records[step + 1]
                    };
                    if handler.decode(va, first, handler.key1) != next {
                        return Err(Error::Invariant(
                            "rewritten ELF has an invalid route".into(),
                        ));
                    }
                    if step + 1 == path.records.len() {
                        let state = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
                        if (!state).wrapping_add(handler.key2)
                            != route_state(seed, route.target, variant)
                        {
                            return Err(Error::Invariant(
                                "rewritten ELF has an invalid route state".into(),
                            ));
                        }
                    }
                    if step > 0 {
                        let second = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
                        let previous = &self.handlers[path.handlers[step - 1]];
                        if previous.decode(va, second, previous.key2) != handler.va {
                            return Err(Error::Invariant(
                                "rewritten ELF has an invalid handler link".into(),
                            ));
                        }
                    }
                }
            }
        }
        for table in &self.tables {
            let function = &selected[table.function].function;
            let source = &function.tables[table.index];
            let bytes = result.content_from_virtual_address(
                table.va,
                (source.targets.len() * source.width()) as u64,
            );
            if bytes.len() != source.targets.len() * source.width() {
                return Err(Error::Invariant(
                    "rewritten ELF has a truncated jump table".into(),
                ));
            }
            for (entry, &target) in source.targets.iter().enumerate() {
                let offset = entry * source.width();
                if !in_range(target, function.start, function.end) {
                    if source.kind != TableKind::Absolute
                        || bytes[offset..offset + 8] != target.to_le_bytes()
                    {
                        return Err(Error::Invariant(
                            "rewritten ELF has an invalid external table pointer".into(),
                        ));
                    }
                    continue;
                }
                let arm = table
                    .unique
                    .binary_search(&target)
                    .map_err(|_| "table target missing")?;
                let (stub, expected) = if selected[table.function].mode() == Mode::Layout {
                    let stub = table.stubs[arm];
                    let mut bytes = ENDBR64.to_vec();
                    bytes.push(0xe9);
                    bytes.extend_from_slice(&rel32(stub + 9, moved[&target])?);
                    (stub, bytes)
                } else {
                    let route = &self.routes[*self
                        .route_index
                        .get(&(
                            table.function,
                            table.source.ok_or("table source missing")?,
                            arm,
                        ))
                        .ok_or("table route missing")?];
                    (
                        route.va,
                        route_stub(
                            route,
                            &self.handlers,
                            self.selectors[route.function],
                            route.guard.map(|index| self.routes[index].va),
                            seed,
                        )?,
                    )
                };
                let pointer = if source.kind == TableKind::Absolute {
                    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
                } else {
                    let delta = i32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap());
                    u64::try_from(table.va as i128 + delta as i128)
                        .map_err(|_| "invalid relative table pointer")?
                };
                if pointer != stub
                    || result.content_from_virtual_address(stub, expected.len() as u64) != expected
                {
                    return Err(Error::Invariant(
                        "rewritten ELF has an invalid jump table".into(),
                    ));
                }
            }
        }
        for placed in &self.dispatches {
            let function = &selected[placed.function].function;
            let source = &function.dispatches[placed.index];
            let source_block = placed
                .source
                .or_else(|| {
                    function
                        .blocks
                        .iter()
                        .find(
                            |block| matches!(block.exit, Exit::Dispatch(id) if id == placed.index),
                        )
                        .map(|block| block.old)
                })
                .ok_or("indexed dispatch source missing")?;
            let branch_end = moved[&source_block] + lengths[&source_block] as u64;
            let mut expected_branch = vec![0xe9];
            expected_branch.extend_from_slice(&rel32(branch_end, placed.va)?);
            if result.content_from_virtual_address(branch_end - 5, 5) != expected_branch {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid indexed dispatch jump".into(),
                ));
            }
            if result.content_from_virtual_address(
                source.original_base,
                source.original_bytes.len() as u64,
            ) != source.original_bytes
            {
                return Err(Error::Invariant(
                    "rewritten ELF changed the original pointer table".into(),
                ));
            }
            let expected = dispatch_code(placed.table_va, source.index, source.notrack)?;
            if result.content_from_virtual_address(placed.va, expected.len() as u64) != expected {
                return Err(Error::Invariant(
                    "rewritten ELF has an invalid indexed dispatcher".into(),
                ));
            }
            let internal: Vec<_> = source
                .targets
                .iter()
                .copied()
                .filter(|&target| in_range(target, function.start, function.end))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let table = result
                .content_from_virtual_address(placed.table_va, (placed.arms.len() * 8) as u64);
            if table.len() != placed.arms.len() * 8 {
                return Err(Error::Invariant(
                    "rewritten ELF has a truncated indexed dispatch table".into(),
                ));
            }
            for (arm, &target) in source.targets.iter().enumerate() {
                let routed = if in_range(target, function.start, function.end) {
                    if selected[placed.function].mode() == Mode::Strong {
                        let route_arm = internal
                            .binary_search(&target)
                            .map_err(|_| "dispatch route target missing")?;
                        self.routes[*self
                            .route_index
                            .get(&(
                                placed.function,
                                placed.source.ok_or("dispatch route source missing")?,
                                route_arm,
                            ))
                            .ok_or("dispatch route missing")?]
                        .va
                    } else {
                        let expected = dispatch_arm_code(
                            placed.arms[arm],
                            *moved.get(&target).ok_or("dispatch target missing")?,
                        )?;
                        if result
                            .content_from_virtual_address(placed.arms[arm], DISPATCH_ARM_LEN as u64)
                            != expected
                        {
                            return Err(Error::Invariant(
                                "rewritten ELF has an invalid indexed dispatch arm".into(),
                            ));
                        }
                        placed.arms[arm]
                    }
                } else {
                    target
                };
                let offset = arm * 8;
                if table[offset..offset + 8] != routed.to_le_bytes() {
                    return Err(Error::Invariant(
                        "rewritten ELF has an invalid indexed dispatch entry".into(),
                    ));
                }
            }
        }
        Ok(())
    }
}

struct Temp {
    path: PathBuf,
    file: File,
}

impl Temp {
    fn new_near(output: &Path) -> Result<Self> {
        let dir = output
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let name = output
            .file_name()
            .ok_or("invalid output path")?
            .to_string_lossy();
        for _ in 0..16 {
            let path = dir.join(format!(
                ".{name}.elfscatter.{}.{:016x}",
                std::process::id(),
                random_seed()?
            ));
            match OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&path)
            {
                Ok(file) => return Ok(Self { path, file }),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
        Err("cannot reserve a temporary output".into())
    }
}

impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn publish(
    bytes: &[u8],
    output: &Path,
    permissions: fs::Permissions,
    map: Option<(&Path, &[u8])>,
) -> Result<()> {
    let mut elf = Temp::new_near(output)?;
    elf.file
        .write_all(bytes)
        .map_err(|e| Error::Io(format!("cannot write output: {e}")))?;
    elf.file.set_permissions(permissions)?;
    elf.file.sync_all()?;
    let map_temp = if let Some((path, bytes)) = map {
        let mut temp = Temp::new_near(path)?;
        temp.file
            .write_all(bytes)
            .map_err(|e| Error::Io(format!("cannot write map: {e}")))?;
        temp.file.sync_all()?;
        Some(temp)
    } else {
        None
    };
    fs::hard_link(&elf.path, output)
        .map_err(|e| Error::Io(format!("cannot create output: {e}")))?;
    if let (Some((path, _)), Some(temp)) = (map, map_temp.as_ref())
        && let Err(error) = fs::hard_link(&temp.path, path)
    {
        return match fs::remove_file(output) {
            Ok(()) => Err(Error::Io(format!("cannot create map: {error}"))),
            Err(rollback) => Err(Error::Io(format!(
                "cannot create map: {error}; cannot roll back {}: {rollback}",
                output.display()
            ))),
        };
    }
    Ok(())
}

fn scrub_bytes(mode: Scrub, len: usize, seed: u64) -> Vec<u8> {
    match mode {
        Scrub::Trap => vec![0xcc; len],
        Scrub::Random => {
            let mut bytes = vec![0; len];
            let mut state = seed ^ 0x6a09e667f3bcc909;
            for chunk in bytes.chunks_mut(8) {
                state = state.wrapping_add(0x9e3779b97f4a7c15);
                let mut word = state;
                word = (word ^ (word >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
                word = (word ^ (word >> 27)).wrapping_mul(0x94d049bb133111eb);
                let word = (word ^ (word >> 31)).to_le_bytes();
                chunk.copy_from_slice(&word[..chunk.len()]);
            }
            bytes
        }
        Scrub::Off => Vec::new(),
    }
}

fn refresh_build_id(binary: &mut elf::Binary, seed: u64) -> Result<Option<(u64, Vec<u8>)>> {
    let Some(section) = binary.section_by_name(".note.gnu.build-id") else {
        return Ok(None);
    };
    let content = section.content();
    if content.len() < 16 {
        return Err("invalid GNU build-id note".into());
    }
    let name_size = u32::from_le_bytes(content[..4].try_into().unwrap()) as usize;
    let desc_size = u32::from_le_bytes(content[4..8].try_into().unwrap()) as usize;
    let note_type = u32::from_le_bytes(content[8..12].try_into().unwrap());
    let desc_offset = 12usize
        .checked_add(
            name_size
                .checked_add(3)
                .ok_or("invalid GNU build-id note")?
                & !3,
        )
        .ok_or("invalid GNU build-id note")?;
    let desc_end = desc_offset
        .checked_add(desc_size)
        .ok_or("invalid GNU build-id note")?;
    if name_size != 4
        || note_type != 3
        || content[12..16] != *b"GNU\0"
        || desc_size == 0
        || desc_end > content.len()
    {
        return Err("invalid GNU build-id note".into());
    }
    let mut state = seed ^ 0x510e527fade682d1;
    for chunk in content[desc_offset..desc_end].chunks(8) {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        state = function_seed(state, u64::from_le_bytes(word));
    }
    let va = section
        .virtual_address()
        .checked_add(desc_offset as u64)
        .ok_or("invalid GNU build-id note")?;
    let bytes = scrub_bytes(Scrub::Random, desc_size, state);
    binary.patch_address(va, &bytes);
    Ok(Some((va, bytes)))
}

struct FrameRegion {
    va: u64,
    len: u32,
    rows: Vec<(u32, UnwindRule)>,
}

fn unwind_rule(rows: &[(u64, UnwindRule)], address: u64) -> Result<UnwindRule> {
    rows.iter()
        .rev()
        .find(|(start, _)| *start <= address)
        .map(|(_, rule)| rule.clone())
        .ok_or_else(|| Error::Invariant(format!("missing unwind row at 0x{address:x}")))
}

fn frame_region(
    function: &Function,
    block: &Block,
    va: u64,
    len: usize,
    scratch: Option<Scratch>,
    references: Option<&BTreeMap<u64, ReferenceSite>>,
) -> Result<FrameRegion> {
    let source = function.unwind.as_ref().ok_or("missing unwind rows")?;
    let prefix =
        usize::from(scratch.is_some_and(|scratch| fragment_endbr(function, block, scratch))) * 4
            + scratch.map_or(0, Scratch::prefix_len);
    let mut boundaries = BTreeMap::new();
    let mut cursor = prefix;
    boundaries.insert(block.old, cursor);
    for instruction in &block.body {
        if function.tables.iter().any(|table| {
            table
                .setup
                .is_some_and(|setup| setup.load == instruction.ip())
        }) {
            cursor += 7;
        }
        if function
            .tables
            .iter()
            .any(|table| table.jump == instruction.ip() && table.setup.is_some())
        {
            cursor += 7;
        }
        boundaries.entry(instruction.ip()).or_insert(cursor);
        cursor += references
            .and_then(|sites| sites.get(&instruction.ip()))
            .map(|site| site.len)
            .unwrap_or(instruction.len());
        boundaries.entry(instruction.next_ip()).or_insert(cursor);
        if let Some(scratch) = scratch
            && matches!(
                instruction.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            )
        {
            cursor += scratch.reset_len();
        }
    }
    let tail_old = block
        .body
        .last()
        .map(Instruction::next_ip)
        .unwrap_or(block.old);
    boundaries.entry(tail_old).or_insert(cursor);
    let mut rows = vec![(0, unwind_rule(source, block.old)?)];
    for (old, rule) in source
        .iter()
        .filter(|(old, _)| *old > block.old && *old <= tail_old)
    {
        let offset = *boundaries
            .get(old)
            .ok_or_else(|| format!("unwind row at 0x{old:x} is not an instruction boundary"))?;
        if offset < len && rows.last().is_none_or(|(_, previous)| previous != rule) {
            rows.push((
                u32::try_from(offset).map_err(|_| "unwind offset out of range")?,
                rule.clone(),
            ));
        }
    }
    Ok(FrameRegion {
        va,
        len: u32::try_from(len).map_err(|_| "unwind region too large")?,
        rows,
    })
}

fn frame_regions(
    layout: &StrongLayout,
    selected: &[Selected],
    image: &CodeImage,
) -> Result<Vec<FrameRegion>> {
    let mut regions = Vec::new();
    let mut fragments_by_function = vec![Vec::new(); selected.len()];
    let mut routes_by_function = vec![Vec::new(); selected.len()];
    let mut tables_by_function = vec![Vec::new(); selected.len()];
    let mut dispatches_by_function = vec![Vec::new(); selected.len()];
    let mut calls_by_function = vec![Vec::new(); selected.len()];
    let mut fragment_by_source = BTreeMap::new();
    for (fragment_index, fragment) in layout.fragments.iter().enumerate() {
        fragments_by_function[fragment.function].push((fragment_index, fragment));
        fragment_by_source.insert((fragment.function, fragment.block.old), fragment);
    }
    for route in &layout.routes {
        routes_by_function[route.function].push(route);
    }
    for table in &layout.tables {
        tables_by_function[table.function].push(table);
    }
    for dispatch in &layout.dispatches {
        dispatches_by_function[dispatch.function].push(dispatch);
    }
    for call in layout.calls.values() {
        calls_by_function[call.function].push(call);
    }
    for (index, item) in selected.iter().enumerate() {
        let Some(rows) = item.function.unwind.as_ref() else {
            continue;
        };
        if item.mode() == Mode::Strong {
            let mut handler_seen = BTreeSet::new();
            for entry in &item.function.entries {
                regions.push(FrameRegion {
                    va: image.entries[&entry.label],
                    len: item.scratch().entry_len() as u32,
                    rows: vec![(0, unwind_rule(rows, entry.label)?)],
                });
            }
            for &(fragment_index, fragment) in &fragments_by_function[index] {
                regions.push(frame_region(
                    &item.function,
                    &fragment.block,
                    fragment.va,
                    image.lengths[&fragment.block.old],
                    Some(item.scratch()),
                    Some(&layout.references),
                )?);
                if layout.startup_smc {
                    let guard = layout
                        .route_index
                        .get(&(index, fragment.block.old, 0))
                        .is_some_and(|&route| layout.routes[route].guard.is_some());
                    if let Some(len) =
                        paired_tail_len(&fragment.block, &item.function, item.scratch(), guard)
                    {
                        let old = fragment
                            .block
                            .body
                            .last()
                            .map(Instruction::next_ip)
                            .unwrap_or(fragment.block.old);
                        regions.push(FrameRegion {
                            va: layout.paired_tails[fragment_index],
                            len: len as u32,
                            rows: vec![(0, unwind_rule(rows, old)?)],
                        });
                    }
                }
            }
            for route in &routes_by_function[index] {
                let fragment = fragment_by_source
                    .get(&(index, route.source))
                    .ok_or("route source missing")?;
                let tail = fragment
                    .block
                    .body
                    .last()
                    .map(Instruction::next_ip)
                    .unwrap_or(fragment.block.old);
                let rule = unwind_rule(rows, tail)?;
                if !route.paired {
                    regions.push(FrameRegion {
                        va: route.va,
                        len: route.stub_len() as u32,
                        rows: vec![(0, rule.clone())],
                    });
                }
                for path in &route.paths {
                    for &handler_index in &path.handlers {
                        if handler_seen.insert(handler_index) {
                            let handler = &layout.handlers[handler_index];
                            regions.push(FrameRegion {
                                va: handler.va,
                                len: handler.code.len() as u32,
                                rows: vec![(0, rule.clone())],
                            });
                        }
                    }
                }
            }
            for call in &calls_by_function[index] {
                regions.push(FrameRegion {
                    va: call.va,
                    len: CALL_STUB_LEN as u32,
                    rows: vec![(
                        0,
                        UnwindRule {
                            cfa_register: 7,
                            cfa_offset: 8,
                            cfa_expression: None,
                            registers: BTreeMap::from([(16, FrameRegisterRule::Offset(-8))]),
                        },
                    )],
                });
            }
        } else if item.mode() == Mode::Layout {
            for block in &item.function.blocks {
                regions.push(frame_region(
                    &item.function,
                    block,
                    image.moved[&block.old],
                    image.lengths[&block.old],
                    None,
                    None,
                )?);
            }
            for table in &tables_by_function[index] {
                for (arm, &target) in table.unique.iter().enumerate() {
                    regions.push(FrameRegion {
                        va: table.stubs[arm],
                        len: 9,
                        rows: vec![(0, unwind_rule(rows, target)?)],
                    });
                }
            }
        }
        for dispatch in &dispatches_by_function[index] {
            let source = &item.function.dispatches[dispatch.index];
            let rule = unwind_rule(rows, source.jump.ip())?;
            let dispatch_len =
                dispatch_code(dispatch.table_va, source.index, source.notrack)?.len();
            regions.push(FrameRegion {
                va: dispatch.va,
                len: dispatch_len as u32,
                rows: vec![(0, rule.clone())],
            });
            for (arm, &va) in dispatch.arms.iter().enumerate() {
                let target = source.targets[arm];
                if item.mode() == Mode::Layout
                    && in_range(target, item.function.start, item.function.end)
                {
                    regions.push(FrameRegion {
                        va,
                        len: DISPATCH_ARM_LEN as u32,
                        rows: vec![(0, unwind_rule(rows, target)?)],
                    });
                }
            }
        }
    }
    Ok(regions)
}

fn uleb(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

fn sleb(mut value: i64, out: &mut Vec<u8>) {
    loop {
        let byte = (value as u8) & 0x7f;
        value >>= 7;
        let done = (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0);
        out.push(byte | if done { 0 } else { 0x80 });
        if done {
            break;
        }
    }
}

fn cfi_rule(rule: &UnwindRule, previous: Option<&UnwindRule>, out: &mut Vec<u8>) {
    if previous.is_none_or(|old| {
        old.cfa_register != rule.cfa_register
            || old.cfa_offset != rule.cfa_offset
            || old.cfa_expression != rule.cfa_expression
    }) {
        if let Some(expression) = &rule.cfa_expression {
            out.push(0x0f);
            uleb(expression.len() as u64, out);
            out.extend_from_slice(expression);
        } else if rule.cfa_offset >= 0 {
            out.push(0x0c);
            uleb(rule.cfa_register.into(), out);
            uleb(rule.cfa_offset as u64, out);
        } else {
            out.push(0x12);
            uleb(rule.cfa_register.into(), out);
            sleb(-(rule.cfa_offset as i64), out);
        }
    }
    if let Some(old) = previous {
        for register in old.registers.keys() {
            if !rule.registers.contains_key(register) {
                out.push(0x06);
                uleb((*register).into(), out);
            }
        }
    }
    for (&register, value) in &rule.registers {
        if previous.and_then(|old| old.registers.get(&register)) == Some(value) {
            continue;
        }
        match value {
            FrameRegisterRule::Undefined => {
                out.push(0x07);
                uleb(register.into(), out);
            }
            FrameRegisterRule::SameValue => {
                out.push(0x08);
                uleb(register.into(), out);
            }
            FrameRegisterRule::Offset(offset) => {
                let factor = -(*offset as i64);
                if factor >= 0 {
                    out.push(0x05);
                    uleb(register.into(), out);
                    uleb(factor as u64, out);
                } else {
                    out.push(0x11);
                    uleb(register.into(), out);
                    sleb(factor, out);
                }
            }
            FrameRegisterRule::ValOffset(offset) => {
                let factor = -(*offset as i64);
                if factor >= 0 {
                    out.push(0x14);
                    uleb(register.into(), out);
                    uleb(factor as u64, out);
                } else {
                    out.push(0x15);
                    uleb(register.into(), out);
                    sleb(factor, out);
                }
            }
            FrameRegisterRule::Register(other) => {
                out.push(0x09);
                uleb(register.into(), out);
                uleb((*other).into(), out);
            }
            FrameRegisterRule::Expression(expression) => {
                out.push(0x10);
                uleb(register.into(), out);
                uleb(expression.len() as u64, out);
                out.extend_from_slice(expression);
            }
        }
    }
}

fn finish_cfi_record(out: &mut Vec<u8>, start: usize, align: usize) -> Result<()> {
    while (out.len() - start) & (align - 1) != 0 {
        out.push(0);
    }
    let length = u32::try_from(out.len() - start - 4).map_err(|_| "unwind record too large")?;
    out[start..start + 4].copy_from_slice(&length.to_le_bytes());
    Ok(())
}

fn write_cfi_rows(region: &FrameRegion, out: &mut Vec<u8>) -> Result<()> {
    let mut last_offset = 0;
    let mut previous: Option<&UnwindRule> = None;
    for (offset, rule) in &region.rows {
        if *offset >= region.len || *offset < last_offset {
            return Err("invalid unwind row offset".into());
        }
        if *offset != last_offset {
            out.push(0x04);
            out.extend_from_slice(&(*offset - last_offset).to_le_bytes());
        }
        cfi_rule(rule, previous, out);
        previous = Some(rule);
        last_offset = *offset;
    }
    Ok(())
}

fn debug_frame_payload(regions: &[FrameRegion], cie_offset: u32) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    let cie = out.len();
    out.extend_from_slice(&[0; 4]);
    out.extend_from_slice(&u32::MAX.to_le_bytes());
    out.extend_from_slice(&[1, 0, 1, 0x7f, 16]);
    finish_cfi_record(&mut out, cie, 8)?;
    for region in regions {
        let start = out.len();
        out.extend_from_slice(&[0; 4]);
        out.extend_from_slice(&cie_offset.to_le_bytes());
        out.extend_from_slice(&region.va.to_le_bytes());
        out.extend_from_slice(&(region.len as u64).to_le_bytes());
        write_cfi_rows(region, &mut out)?;
        finish_cfi_record(&mut out, start, 8)?;
    }
    Ok(out)
}

fn compressed_debug_frame(frame: &[u8]) -> Result<Vec<u8>> {
    if frame.len() > 128 * 1024 * 1024 {
        return Err("debug frame exceeds size limit".into());
    }
    let data = miniz_oxide::deflate::compress_to_vec_zlib(frame, 9);
    let mut out = Vec::with_capacity(24 + data.len());
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes());
    out.extend_from_slice(&(frame.len() as u64).to_le_bytes());
    out.extend_from_slice(&8u64.to_le_bytes());
    out.extend_from_slice(&data);
    Ok(out)
}

fn debug_frame_prefix(data: &[u8]) -> Result<&[u8]> {
    let mut offset = 0usize;
    while offset < data.len() {
        let rest = &data[offset..];
        if rest.len() < 4 {
            return if rest.iter().all(|byte| *byte == 0) {
                Ok(&data[..offset])
            } else {
                Err("truncated debugger frame record".into())
            };
        }
        let length = u32::from_le_bytes(rest[..4].try_into().unwrap());
        if length == 0 {
            return if rest.iter().all(|byte| *byte == 0) {
                Ok(&data[..offset])
            } else {
                Err("invalid debugger frame terminator".into())
            };
        }
        let record = if length == u32::MAX {
            if rest.len() < 12 {
                return Err("truncated debugger frame record".into());
            }
            let length = u64::from_le_bytes(rest[4..12].try_into().unwrap());
            usize::try_from(length)
                .ok()
                .and_then(|length| length.checked_add(12))
        } else {
            (length as usize).checked_add(4)
        }
        .ok_or("debugger frame record too large")?;
        offset = offset
            .checked_add(record)
            .filter(|end| *end <= data.len())
            .ok_or("truncated debugger frame record")?;
    }
    Ok(data)
}

fn debug_frame_ranges(data: &[u8]) -> Result<Vec<(u64, u64)>> {
    let frame = DebugFrame::new(data, LittleEndian);
    let bases = BaseAddresses::default();
    let mut entries = frame.entries(&bases);
    let mut ranges = Vec::new();
    while let Some(entry) = entries
        .next()
        .map_err(|e| format!("invalid debugger FDE: {e}"))?
    {
        if let CieOrFde::Fde(partial) = entry {
            let fde = partial
                .parse(|section, bases, offset| section.cie_from_offset(bases, offset))
                .map_err(|e| format!("invalid debugger FDE: {e}"))?;
            ranges.push((fde.initial_address(), fde.end_address()));
        }
    }
    Ok(ranges)
}

fn unwind_payload(
    index: &AnalysisIndex,
    regions: &[FrameRegion],
    base: u64,
    old_base: u64,
) -> Result<(Vec<u8>, usize, usize)> {
    let mut out = Vec::new();
    let cie = out.len();
    out.extend_from_slice(&[0; 8]);
    out.extend_from_slice(&[1, b'z', b'R', 0, 1]);
    sleb(-1, &mut out);
    out.extend_from_slice(&[16, 1, 0x1b]);
    finish_cfi_record(&mut out, cie, 4)?;

    let mut table: Vec<(u64, u64)> = index
        .fdes
        .iter()
        .filter(|fde| fde.end > fde.start)
        .map(|fde| (fde.start, old_base + fde.offset as u64))
        .collect();
    for region in regions {
        let start = out.len();
        out.extend_from_slice(&[0; 4]);
        let cie_pointer =
            u32::try_from(start + 4 - cie).map_err(|_| "unwind CIE pointer out of range")?;
        out.extend_from_slice(&cie_pointer.to_le_bytes());
        let initial = region.va as i128 - (base + out.len() as u64) as i128;
        out.extend_from_slice(
            &i32::try_from(initial)
                .map_err(|_| "unwind address out of range")?
                .to_le_bytes(),
        );
        out.extend_from_slice(&region.len.to_le_bytes());
        out.push(0);
        write_cfi_rows(region, &mut out)?;
        finish_cfi_record(&mut out, start, 4)?;
        table.push((region.va, base + start as u64));
    }
    out.extend_from_slice(&[0; 4]);
    while (base + out.len() as u64) & 3 != 0 {
        out.push(0);
    }
    let header_offset = out.len();
    let header_va = base + header_offset as u64;
    out.extend_from_slice(&[1, 0x1b, 0x03, 0x3b]);
    let old_pointer = old_base as i128 - (base + out.len() as u64) as i128;
    out.extend_from_slice(
        &i32::try_from(old_pointer)
            .map_err(|_| "unwind header pointer out of range")?
            .to_le_bytes(),
    );
    table.sort_unstable_by_key(|&(start, _)| start);
    out.extend_from_slice(
        &u32::try_from(table.len())
            .map_err(|_| "too many unwind entries")?
            .to_le_bytes(),
    );
    for (start, fde) in table {
        out.extend_from_slice(
            &i32::try_from(start as i128 - header_va as i128)
                .map_err(|_| "unwind table address out of range")?
                .to_le_bytes(),
        );
        out.extend_from_slice(
            &i32::try_from(fde as i128 - header_va as i128)
                .map_err(|_| "unwind table FDE out of range")?
                .to_le_bytes(),
        );
    }
    let header_len = out.len() - header_offset;
    Ok((out, header_offset, header_len))
}

fn patch_unwind_header(
    bytes: &mut [u8],
    binary: &elf::Binary,
    base: u64,
    header_va: u64,
    size: usize,
) -> Result<()> {
    let segment = binary
        .segments()
        .find(|seg| seg.p_type() == segment::Type::LOAD && seg.virtual_address() == base)
        .ok_or("new load segment missing")?;
    let file_offset = segment
        .file_offset()
        .checked_add(
            header_va
                .checked_sub(base)
                .ok_or("unwind address underflow")?,
        )
        .ok_or("unwind file offset overflow")?;
    let section_index = binary
        .section_idx_by_name(".eh_frame_hdr")
        .ok_or("missing .eh_frame_hdr section")?;
    let mut phdr = None;
    for i in 0..elf_u16(bytes, 56)? as usize {
        let offset = header_entry(bytes, false, i)?;
        if elf_u32(bytes, offset)? == 0x6474e550 && phdr.replace(offset).is_some() {
            return Err("multiple PT_GNU_EH_FRAME headers".into());
        }
    }
    let phdr = phdr.ok_or("missing PT_GNU_EH_FRAME")?;
    let shdr = header_entry(bytes, true, section_index)?;
    let length = u64::try_from(size).map_err(|_| "unwind header too large")?;
    for (offset, value) in [
        (phdr + 8, file_offset),
        (phdr + 16, header_va),
        (phdr + 24, header_va),
        (phdr + 32, length),
        (phdr + 40, length),
        (shdr + 16, header_va),
        (shdr + 24, file_offset),
        (shdr + 32, length),
    ] {
        bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }
    Ok(())
}

fn append_aligned(bytes: &mut Vec<u8>, content: &[u8]) -> Result<u64> {
    while bytes.len() & 7 != 0 {
        bytes.push(0);
    }
    let offset = u64::try_from(bytes.len()).map_err(|_| "ELF file offset out of range")?;
    bytes.extend_from_slice(content);
    Ok(offset)
}

struct DebugFrameOutput {
    plain: Vec<u8>,
    compressed: Vec<u8>,
    file_offset: u64,
    ranges: Vec<(u64, u64)>,
}

fn append_debug_frame(bytes: &mut Vec<u8>, regions: &[FrameRegion]) -> Result<DebugFrameOutput> {
    let binary = parse_elf(bytes)?;
    let mut sections = binary
        .sections()
        .filter(|section| section.name() == ".debug_frame");
    let existing = sections.next();
    if sections.next().is_some() {
        return Err("multiple debugger frame sections".into());
    }
    let section_index = binary.section_idx_by_name(".debug_frame");
    let mut plain = Vec::new();
    let mut ranges = Vec::new();
    if let Some(section) = existing {
        if section.get_type() != section::Type::PROGBITS
            || section.flags().contains(section::Flags::ALLOC)
            || section.virtual_address() != 0
        {
            return Err("unsupported debugger frame section".into());
        }
        let content = section.content();
        if section.flags().contains(section::Flags::COMPRESSED) {
            if content.len() < 24
                || u32::from_le_bytes(content[..4].try_into().unwrap()) != 1
                || content[4..8] != [0; 4]
            {
                return Err("unsupported debugger frame compression".into());
            }
            let size = u64::from_le_bytes(content[8..16].try_into().unwrap());
            if size > 128 * 1024 * 1024 {
                return Err("debug frame exceeds size limit".into());
            }
            plain = miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(
                &content[24..],
                size as usize,
            )
            .map_err(|_| "cannot decompress debugger frame data")?;
            if plain.len() != size as usize {
                return Err("invalid debugger frame compression".into());
            }
        } else {
            plain.extend_from_slice(content);
        }
        plain.truncate(debug_frame_prefix(&plain)?.len());
        ranges = debug_frame_ranges(&plain)?;
    }
    let cie_offset = u32::try_from(plain.len()).map_err(|_| "debug frame exceeds size limit")?;
    plain.extend_from_slice(&debug_frame_payload(regions, cie_offset)?);
    let compressed = compressed_debug_frame(&plain)?;
    ranges.extend(
        regions
            .iter()
            .map(|region| (region.va, region.va + region.len as u64)),
    );
    let shentsize = elf_u16(bytes, 58)? as usize;
    let shnum = elf_u16(bytes, 60)? as usize;
    let shstrndx = elf_u16(bytes, 62)? as usize;
    if shnum == 0 || shnum >= 0xff00 || (section_index.is_none() && shnum >= 0xfeff) {
        return Err("unsupported ELF section table".into());
    }
    let shoff = header_entry(bytes, true, 0)?;
    let end = header_entry(bytes, true, shnum - 1)? + shentsize;
    let mut table = bytes[shoff..end].to_vec();
    let shstr = header_entry(bytes, true, shstrndx)? - shoff;
    if elf_u32(&table, shstr + 4)? != 3 {
        return Err("invalid section-name table".into());
    }
    let names = file_range(
        bytes.len(),
        elf_u64(&table, shstr + 24)?,
        elf_u64(&table, shstr + 32)?,
    )?;
    if names.is_empty() || bytes[names.end - 1] != 0 {
        return Err("invalid section-name table".into());
    }
    let names_size = names.len();
    let section_offset = append_aligned(bytes, &compressed)?;
    let index = if let Some(index) = section_index {
        if index >= shnum {
            return Err("invalid debugger frame section index".into());
        }
        index
    } else {
        let mut names = bytes[names].to_vec();
        names.extend_from_slice(b".debug_frame\0");
        let new_names_offset = append_aligned(bytes, &names)?;
        table[shstr + 24..shstr + 32].copy_from_slice(&new_names_offset.to_le_bytes());
        table[shstr + 32..shstr + 40].copy_from_slice(&(names.len() as u64).to_le_bytes());
        table.extend_from_slice(&[0u8; 64]);
        shnum
    };
    let header = index * shentsize;
    if section_index.is_none() {
        let name = u32::try_from(names_size).map_err(|_| "section-name table too large")?;
        table[header..header + 4].copy_from_slice(&name.to_le_bytes());
    }
    table[header + 4..header + 8].copy_from_slice(&1u32.to_le_bytes());
    table[header + 8..header + 16]
        .copy_from_slice(&section::Flags::COMPRESSED.bits().to_le_bytes());
    table[header + 16..header + 24].copy_from_slice(&0u64.to_le_bytes());
    table[header + 24..header + 32].copy_from_slice(&section_offset.to_le_bytes());
    table[header + 32..header + 40].copy_from_slice(&(compressed.len() as u64).to_le_bytes());
    table[header + 48..header + 56].copy_from_slice(&8u64.to_le_bytes());
    let new_shoff = append_aligned(bytes, &table)?;
    bytes[40..48].copy_from_slice(&new_shoff.to_le_bytes());
    if section_index.is_none() {
        bytes[60..62].copy_from_slice(&((shnum + 1) as u16).to_le_bytes());
    }
    Ok(DebugFrameOutput {
        plain,
        compressed,
        file_offset: section_offset,
        ranges,
    })
}

struct Rewrite {
    start: u64,
    bytes: Vec<u8>,
}

struct SourceRewrite {
    address: u64,
    original: [u8; 4],
    bytes: [u8; 4],
}

enum RewriteOutcome {
    Complete,
    UnreachableSource(u64),
    UnaddressableTable(u64),
    VmUnrepresentable(u64, String),
}

#[derive(Clone, Copy)]
struct UnwindHeader {
    address: u64,
    length: usize,
    regions: usize,
}

struct PreparedImage {
    binary: elf::Binary,
    base: u64,
    data_base: Option<u64>,
    image: CodeImage,
    vm_image: Option<vm::VmImage>,
    plain_protected: Vec<u8>,
    unwind_header: Option<UnwindHeader>,
}

fn rewrite(
    input: &Snapshot,
    index: &AnalysisIndex,
    opts: &Options,
    selected: &[Selected],
    seed: u64,
    skipped: usize,
    report: &mut String,
) -> Result<RewriteOutcome> {
    let binary = parse_elf(&input.bytes)?;
    let output = opts.output.as_ref().unwrap();
    let map = opts.map.as_deref();
    let scrub = opts.scrub;
    let old_loads: Vec<u64> = binary
        .segments()
        .filter(|s| s.p_type() == segment::Type::LOAD)
        .map(|s| s.virtual_address())
        .collect();
    let old_relro: Vec<_> = binary
        .segments()
        .filter(|s| s.p_type() == segment::Type::GNU_RELRO)
        .map(|s| (s.virtual_address(), s.virtual_size()))
        .collect();
    let mut old_relative_relocations: Vec<_> = binary
        .relocations()
        .filter(|rel| {
            rel.get_type() == relocation::Type::X86_64_RELATIVE
                && rel.purpose() == relocation::Purpose::DYNAMIC
        })
        .map(|rel| (rel.address(), rel.addend(), rel.is_rela()))
        .collect();
    old_relative_relocations.sort_unstable();
    let old_interpreter = binary.interpreter();
    let old_entrypoint = binary.header().entrypoint();
    let original_tables: Vec<_> = selected
        .iter()
        .flat_map(|item| item.function.tables.iter())
        .filter(|table| table.kind == TableKind::Absolute)
        .map(|table| {
            (
                table.original_base,
                binary
                    .content_from_virtual_address(
                        table.original_base,
                        (table.targets.len() * table.width()) as u64,
                    )
                    .to_vec(),
            )
        })
        .collect();
    let original_fixed_slots: Vec<_> = selected
        .iter()
        .flat_map(|item| item.function.fixed_slots.iter())
        .map(|&slot| (slot, binary.content_from_virtual_address(slot, 8).to_vec()))
        .collect();
    let mut old_dynamic: Vec<_> = binary
        .dynamic_symbols()
        .map(|s| (s.name(), s.value(), s.size()))
        .collect();
    old_dynamic.sort();
    let vm_present = selected.iter().any(|item| item.mode() == Mode::Vm);
    let has_unwind = vm_present || selected.iter().any(|item| item.function.unwind.is_some());
    let old_eh_va = if has_unwind {
        Some(
            binary
                .section_by_name(".eh_frame")
                .ok_or("missing .eh_frame")?
                .virtual_address(),
        )
    } else {
        None
    };
    if has_unwind
        && !binary
            .segments()
            .any(|seg| seg.p_type() == segment::Type::GNU_EH_FRAME)
    {
        return Err("unwind-covered functions require PT_GNU_EH_FRAME".into());
    }
    let old_unwind: Vec<_> = if has_unwind {
        vec![".eh_frame"]
    } else {
        vec![".eh_frame", ".eh_frame_hdr"]
    }
    .into_iter()
    .filter_map(|name| {
        binary
            .section_by_name(name)
            .map(|sec| (name, sec.content().to_vec()))
    })
    .collect();
    let mut layout = StrongLayout::new(&binary, selected, seed, opts.startup_smc)?;
    let vm_start = if vm_present {
        align_up(layout.capacity, 4096)?
    } else {
        0
    };
    let vm_len = if vm_present {
        vm::capacity(selected)?
    } else {
        0
    };
    let startup_enabled = opts.startup_smc && (layout.startup_smc || vm_present);
    let region_start = if layout.startup_smc {
        layout.protected_start
    } else {
        vm_start
    };
    let vm_end = vm_start.checked_add(vm_len).ok_or("VM region overflow")?;
    let region_end = if vm_present {
        align_up(vm_end, 4096)?
    } else {
        layout.protected_end
    };
    let payload_capacity = if vm_present {
        if startup_enabled { region_end } else { vm_end }
    } else {
        layout.capacity
    };
    let metadata_capacity = if startup_enabled {
        preinit_input(&binary)?;
        startup_metadata_capacity(&binary)?
    } else {
        0
    };
    let code_capacity = payload_capacity
        .checked_add(if startup_enabled { 4096 } else { 0 })
        .ok_or("code region overflow")?;
    let extra = if has_unwind { 4096 } else { 0 };
    let trailer_pad = if has_unwind {
        (4 - code_capacity % 4) % 4
    } else {
        0
    };
    let mut size = code_capacity
        .checked_add(trailer_pad)
        .and_then(|n| n.checked_add(extra))
        .ok_or("clone length overflow")?;
    let mut first = Some(binary);
    let mut prepared = None;
    for _ in 0..4 {
        let mut candidate = if let Some(original) = first.take() {
            original
        } else {
            parse_elf(&input.bytes)?
        };
        if candidate.relocate_phdr_table(elf::binary::PhdrReloc::SEGMENT_GAP) == 0 {
            return Err("no segment gap available for the program header table".into());
        }
        let mut segment = elf::Segment::new();
        segment.set_type(segment::Type::LOAD);
        segment.set_flags(segment::Flags::R | segment::Flags::X);
        segment.set_alignment(0x1000);
        segment.set_content(&vec![0xcc; size]);
        let added = candidate
            .add_segment(&segment)
            .ok_or("cannot add executable PT_LOAD")?;
        let base = added.virtual_address();
        base.checked_add(size as u64)
            .and_then(|end| end.checked_add(128 * 1024 * 1024))
            .ok_or("clone address range overflow")?;
        let data_base = if startup_enabled {
            let mut data = elf::Segment::new();
            data.set_type(segment::Type::LOAD);
            data.set_flags(segment::Flags::R | segment::Flags::W);
            data.set_alignment(0x1000);
            data.set_content(&vec![0; metadata_capacity]);
            Some(
                candidate
                    .add_segment(&data)
                    .ok_or("cannot add startup metadata PT_LOAD")?
                    .virtual_address(),
            )
        } else {
            None
        };
        layout.place(base, selected)?;
        if let Some(table) = layout.tables.iter().find(|table| {
            selected[table.function].function.tables[table.index].kind == TableKind::Absolute
                && !i32::try_from(table.va as i64).is_ok_and(|disp| disp as i64 as u64 == table.va)
        }) {
            return Ok(RewriteOutcome::UnaddressableTable(
                selected[table.function].function.start,
            ));
        }
        if let Some(table) = layout.dispatches.iter().find(|table| {
            !i32::try_from(table.table_va as i64)
                .is_ok_and(|disp| disp as i64 as u64 == table.table_va)
        }) {
            return Ok(RewriteOutcome::UnaddressableTable(
                selected[table.function].function.start,
            ));
        }
        let mut image = layout.encode(selected, seed).map_err(Error::invariant)?;
        let vm_image = if vm_present {
            let placed = match vm::encode(selected, &image.entries, base + vm_start as u64, seed) {
                Ok(placed) => placed,
                Err(vm::VmFailure {
                    address,
                    reason: Error::Unsupported(reason),
                }) => {
                    return Ok(RewriteOutcome::VmUnrepresentable(address, reason));
                }
                Err(error) => return Err(error.reason),
            };
            image.code.resize(vm_start + placed.code.len(), 0xcc);
            image.code[vm_start..vm_start + placed.code.len()].copy_from_slice(&placed.code);
            image
                .entries
                .extend(placed.entries.iter().map(|(&old, &new)| (old, new)));
            image
                .moved
                .extend(placed.moved.iter().map(|(&old, &new)| (old, new)));
            image
                .lengths
                .extend(placed.lengths.iter().map(|(&old, &len)| (old, len)));
            Some(placed)
        } else {
            None
        };
        let mut plain_protected = Vec::new();
        if startup_enabled {
            image.code.resize(region_end, 0xcc);
            let route_va = base + region_start as u64;
            let route_len = region_end - region_start;
            let decoder = startup_decoder(
                base + payload_capacity as u64,
                route_va,
                route_len,
                startup_key(seed),
            )?;
            plain_protected.extend_from_slice(&image.code[region_start..region_end]);
            mask_startup_code(&mut image.code[region_start..region_end], startup_key(seed))?;
            image.code.resize(code_capacity, 0xcc);
            image.code[payload_capacity..payload_capacity + decoder.len()]
                .copy_from_slice(&decoder);
        }
        let unwind_header = if has_unwind {
            let mut regions = frame_regions(&layout, selected, &image)?;
            if let Some(placed) = &vm_image {
                regions.extend(vm::frame_regions(placed, selected)?);
            }
            image.code.resize(code_capacity + trailer_pad, 0xcc);
            let (payload, offset, len) = unwind_payload(
                index,
                &regions,
                base + code_capacity as u64 + trailer_pad as u64,
                old_eh_va.unwrap(),
            )?;
            if payload.len() > 128 * 1024 * 1024 {
                return Err("unwind metadata exceeds size limit".into());
            }
            image.code.extend_from_slice(&payload);
            Some(UnwindHeader {
                address: base + code_capacity as u64 + trailer_pad as u64 + offset as u64,
                length: len,
                regions: regions.len(),
            })
        } else {
            None
        };
        if image.code.len() == size {
            prepared = Some(PreparedImage {
                binary: candidate,
                base,
                data_base,
                image,
                vm_image,
                plain_protected,
                unwind_header,
            });
            break;
        }
        size = image.code.len();
    }
    let PreparedImage {
        mut binary,
        base,
        data_base,
        image,
        vm_image,
        plain_protected,
        unwind_header,
    } = prepared.ok_or_else(|| Error::Invariant("added segment size did not converge".into()))?;
    let debug_regions = if has_unwind {
        let mut regions = frame_regions(&layout, selected, &image)?;
        if let Some(placed) = &vm_image {
            regions.extend(vm::frame_regions(placed, selected)?);
        }
        Some(regions)
    } else {
        None
    };
    let mut selected_ranges: Vec<(u64, u64)> = Vec::new();
    for item in selected {
        if let Some((_, end)) = selected_ranges.last_mut()
            && item.function.start <= *end
        {
            *end = (*end).max(item.function.end);
        } else {
            selected_ranges.push((item.function.start, item.function.end));
        }
    }
    let mut rewritten = Vec::with_capacity(selected.len());
    let mut sources = BTreeMap::new();
    for item in selected {
        let function = &item.function;
        let mut bytes = if scrub == Scrub::Off {
            function.bytes.clone()
        } else {
            scrub_bytes(
                scrub,
                function.bytes.len(),
                function_seed(seed, function.start),
            )
        };
        for entry in &function.entries {
            if let Some((patch, len)) = entry.window {
                let offset = (patch - function.start) as usize;
                if patch != entry.label {
                    let label_offset = (entry.label - function.start) as usize;
                    bytes[label_offset..label_offset + 4].copy_from_slice(&ENDBR64);
                }
                bytes[offset] = 0xe9;
                bytes[offset + 1..offset + 5]
                    .copy_from_slice(&rel32(patch + 5, image.entries[&entry.label])?);
                if scrub == Scrub::Off {
                    bytes[offset + 5..offset + len].fill(0x90);
                }
            } else {
                for source in &entry.sources {
                    let at = selected_ranges.partition_point(|&(start, _)| start <= source.source);
                    if at != 0 && source.source < selected_ranges[at - 1].1 {
                        continue;
                    }
                    let target = image.entries[&entry.label];
                    let Ok(branch) = rel32(source.next, target) else {
                        return Ok(RewriteOutcome::UnreachableSource(function.start));
                    };
                    let site = SourceRewrite {
                        address: source.address,
                        original: source.original,
                        bytes: branch,
                    };
                    if sources.insert(source.address, site).is_some() {
                        return Err("duplicate retained source".into());
                    }
                }
            }
        }
        rewritten.push(Rewrite {
            start: function.start,
            bytes,
        });
    }
    binary.patch_address(base, &image.code);
    for item in &rewritten {
        binary.patch_address(item.start, &item.bytes);
    }
    for site in sources.values() {
        if binary.content_from_virtual_address(site.address, 4) != site.original {
            return Err("retained source changed before patching".into());
        }
        binary.patch_address(site.address, &site.bytes);
    }
    let new_build_id = if !opts.keep_metadata {
        binary.strip();
        let removable: Vec<_> = binary
            .sections()
            .filter(|section| {
                !section.flags().contains(section::Flags::ALLOC)
                    && (section.name() == ".strtab"
                        || section.name().starts_with(".debug_")
                        || section.name().starts_with(".zdebug_"))
            })
            .map(|section| section.name())
            .collect();
        if !removable.is_empty() {
            let shadow = parse_elf(&binary.write_to_bytes())?;
            for name in removable {
                if let Some(section) = shadow.section_by_name(&name) {
                    binary.remove_section(&section, true);
                    if binary.has_section(&name) {
                        return Err(format!("cannot remove {name} section").into());
                    }
                }
            }
        }
        refresh_build_id(&mut binary, seed)?
    } else {
        None
    };

    let mut output_bytes = binary.write_to_bytes();
    drop(binary);
    validate_elf_bytes(&output_bytes).map_err(Error::invariant)?;
    if let Some(UnwindHeader {
        address: header_va,
        length: header_len,
        ..
    }) = unwind_header
    {
        let preliminary = parse_elf(&output_bytes).map_err(Error::invariant)?;
        patch_unwind_header(&mut output_bytes, &preliminary, base, header_va, header_len)?;
    }
    let debug_frame = if let Some(regions) = &debug_regions {
        Some(append_debug_frame(&mut output_bytes, regions)?)
    } else {
        None
    };
    if let Some(data_va) = data_base {
        patch_startup_metadata(
            &mut output_bytes,
            data_va,
            metadata_capacity,
            base + payload_capacity as u64,
        )?;
    }
    let mut result = parse_elf(&output_bytes).map_err(Error::invariant)?;
    for (base, bytes) in &original_tables {
        if result.content_from_virtual_address(*base, bytes.len() as u64) != *bytes {
            return Err(Error::Invariant(
                "rewritten ELF changed an original absolute table".into(),
            ));
        }
    }
    for (slot, bytes) in &original_fixed_slots {
        if bytes.len() != 8 || result.content_from_virtual_address(*slot, 8) != *bytes {
            return Err(Error::Invariant(
                "rewritten ELF changed an original pointer slot".into(),
            ));
        }
    }
    let phdr = result
        .segments()
        .find(|s| s.p_type() == segment::Type::PHDR)
        .ok_or("rewritten ELF has no PT_PHDR")?;
    let phdr_loaded = result.segments().any(|s| {
        s.p_type() == segment::Type::LOAD
            && s.flags() & segment::Flags::R.bits() != 0
            && phdr.virtual_address() >= s.virtual_address()
            && phdr.virtual_address().saturating_add(phdr.virtual_size())
                <= s.virtual_address().saturating_add(s.physical_size())
    });
    if result.interpreter() != old_interpreter
        || result.header().entrypoint() != old_entrypoint
        || phdr.file_offset() != result.header().program_headers_offset()
        || !phdr_loaded
    {
        return Err(Error::Invariant(
            "rewritten ELF has invalid loader metadata".into(),
        ));
    }
    let mut new_dynamic: Vec<_> = result
        .dynamic_symbols()
        .map(|s| (s.name(), s.value(), s.size()))
        .collect();
    new_dynamic.sort();
    if new_dynamic != old_dynamic {
        return Err(Error::Invariant(
            "rewritten ELF changed dynamic symbols".into(),
        ));
    }
    let new_relro: Vec<_> = result
        .segments()
        .filter(|s| s.p_type() == segment::Type::GNU_RELRO)
        .map(|s| (s.virtual_address(), s.virtual_size()))
        .collect();
    let mut new_relative_relocations: Vec<_> = result
        .relocations()
        .filter(|rel| {
            rel.get_type() == relocation::Type::X86_64_RELATIVE
                && rel.purpose() == relocation::Purpose::DYNAMIC
        })
        .map(|rel| (rel.address(), rel.addend(), rel.is_rela()))
        .collect();
    new_relative_relocations.sort_unstable();
    let old_relocations_preserved = if startup_enabled {
        old_relative_relocations
            .iter()
            .all(|rel| new_relative_relocations.binary_search(rel).is_ok())
    } else {
        new_relative_relocations == old_relative_relocations
    };
    if new_relro != old_relro || !old_relocations_preserved {
        return Err(Error::Invariant(
            "rewritten ELF changed RELRO or relative relocations".into(),
        ));
    }
    for (name, content) in old_unwind {
        if result.section_by_name(name).is_none_or(|sec| {
            sec.content() != content
                || (name == ".eh_frame" && old_eh_va.is_some_and(|va| sec.virtual_address() != va))
        }) {
            return Err(format!("rewritten ELF changed {name}").into());
        }
    }
    if let Some(frame) = &debug_frame {
        let mut sections = result.sections().filter(|sec| sec.name() == ".debug_frame");
        let section = sections
            .next()
            .ok_or("rewritten ELF has no debugger frame section")?;
        if sections.next().is_some() {
            return Err(Error::Invariant(
                "rewritten ELF has multiple debugger frame sections".into(),
            ));
        }
        if section.get_type() != section::Type::PROGBITS
            || !section.flags().contains(section::Flags::COMPRESSED)
            || section.flags().contains(section::Flags::ALLOC)
            || section.virtual_address() != 0
            || section.file_offset() != frame.file_offset
            || section.size() != frame.compressed.len() as u64
        {
            return Err(Error::Invariant(
                "rewritten ELF has an invalid debugger frame section".into(),
            ));
        }
        let offset = usize::try_from(section.file_offset())
            .map_err(|_| "debugger frame offset out of range")?;
        let end = offset
            .checked_add(frame.compressed.len())
            .ok_or("debugger frame range out of bounds")?;
        if output_bytes.get(offset..end) != Some(frame.compressed.as_slice()) {
            return Err(Error::Invariant(
                "rewritten ELF changed debugger frame data".into(),
            ));
        }
        let decoded = miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(
            &frame.compressed[24..],
            frame.plain.len(),
        )
        .map_err(|_| "cannot decompress debugger frame data")?;
        if decoded != frame.plain {
            return Err("invalid debugger frame compression".into());
        }
        let mut actual = debug_frame_ranges(&frame.plain)?;
        let mut expected = frame.ranges.clone();
        actual.sort_unstable();
        expected.sort_unstable();
        if actual != expected {
            return Err("debugger FDE ranges do not match moved code".into());
        }
    }
    if !opts.keep_metadata
        && (result
            .sections()
            .filter(|s| s.name() == ".debug_frame")
            .count()
            != usize::from(debug_frame.is_some())
            || result.sections().any(|s| {
                s.name() == ".symtab"
                    || s.name() == ".strtab"
                    || (s.name().starts_with(".debug_") && s.name() != ".debug_frame")
                    || s.name().starts_with(".zdebug_")
            }))
    {
        return Err(Error::Invariant(
            "rewritten ELF retains static symbols or debug sections".into(),
        ));
    }
    if let Some((va, bytes)) = new_build_id
        && result.content_from_virtual_address(va, bytes.len() as u64) != bytes
    {
        return Err(Error::Invariant(
            "rewritten ELF has an invalid build ID".into(),
        ));
    }
    let new_loads: BTreeSet<u64> = result
        .segments()
        .filter(|s| s.p_type() == segment::Type::LOAD)
        .map(|s| s.virtual_address())
        .collect();
    if !old_loads.iter().all(|va| new_loads.contains(va)) {
        return Err(format!(
            "ELF writer moved an existing PT_LOAD: {old_loads:x?} -> {new_loads:x?}"
        )
        .into());
    }
    let new_segment = result
        .segments()
        .find(|s| s.p_type() == segment::Type::LOAD && s.virtual_address() == base)
        .ok_or("new PT_LOAD missing after write")?;
    if new_segment.flags() & (segment::Flags::R | segment::Flags::X).bits()
        != (segment::Flags::R | segment::Flags::X).bits()
        || new_segment.flags() & segment::Flags::W.bits() != 0
        || result.content_from_virtual_address(base, image.code.len() as u64) != image.code
    {
        return Err(Error::Invariant(
            "rewritten ELF failed structural verification".into(),
        ));
    }
    if let Some(data_va) = data_base {
        let protected_start = base + region_start as u64;
        let protected_end = base + region_end as u64;
        for relocation in result.relocations() {
            let address = relocation.address();
            let len = relocation.size().div_ceil(8);
            let end = address
                .checked_add(len)
                .ok_or("relocation address overflow")?;
            if address < protected_end && end > protected_start {
                return Err(Error::Unsupported(format!(
                    "relocation at 0x{address:x} writes startup-protected code"
                )));
            }
        }
        verify_startup_metadata(
            &input.bytes,
            &result,
            data_va,
            base + payload_capacity as u64,
            base + region_start as u64,
            region_end - region_start,
            seed,
        )?;
    }
    if result.segments().any(|s| {
        s.p_type() == segment::Type::LOAD
            && s.flags() & (segment::Flags::W | segment::Flags::X).bits()
                == (segment::Flags::W | segment::Flags::X).bits()
    }) {
        return Err(Error::Invariant(
            "rewritten ELF has a writable executable segment".into(),
        ));
    }
    if let Some(UnwindHeader {
        address: header_va,
        length: header_len,
        regions: expected,
    }) = unwind_header
    {
        let header = result
            .segments()
            .find(|seg| seg.p_type() == segment::Type::GNU_EH_FRAME)
            .ok_or("rewritten ELF has no unwind header")?;
        let section = result
            .section_by_name(".eh_frame_hdr")
            .ok_or("rewritten ELF has no unwind header section")?;
        if header.virtual_address() != header_va
            || header.physical_size() != header_len as u64
            || section.virtual_address() != header_va
            || section.content()
                != result.content_from_virtual_address(header_va, header_len as u64)
        {
            return Err(Error::Invariant(
                "rewritten ELF has an invalid unwind header".into(),
            ));
        }
        let trailer = base + code_capacity as u64 + trailer_pad as u64;
        let bytes = result.content_from_virtual_address(trailer, header_va - trailer);
        let frame = EhFrame::new(bytes, LittleEndian);
        let bases = BaseAddresses::default().set_eh_frame(trailer);
        let mut entries = frame.entries(&bases);
        let mut found = 0;
        while let Some(entry) = entries
            .next()
            .map_err(|e| format!("invalid supplemental FDE: {e}"))?
        {
            if let CieOrFde::Fde(partial) = entry {
                partial
                    .parse(|section, bases, offset| section.cie_from_offset(bases, offset))
                    .map_err(|e| format!("invalid supplemental FDE: {e}"))?;
                found += 1;
            }
        }
        if found != expected {
            return Err("supplemental FDE count mismatch".into());
        }
    }
    for item in &rewritten {
        if result.content_from_virtual_address(item.start, item.bytes.len() as u64) != item.bytes {
            return Err(Error::Invariant(
                "rewritten ELF failed entry verification".into(),
            ));
        }
    }
    for site in sources.values() {
        if result.content_from_virtual_address(site.address, 4) != site.bytes {
            return Err(Error::Invariant(
                "rewritten ELF failed source verification".into(),
            ));
        }
    }
    if startup_enabled {
        let route_va = base + region_start as u64;
        let route_len = region_end - region_start;
        let mut decoded = result
            .content_from_virtual_address(route_va, route_len as u64)
            .to_vec();
        if decoded.len() != route_len {
            return Err("truncated encoded route region".into());
        }
        mask_startup_code(&mut decoded, startup_key(seed))?;
        if decoded != plain_protected {
            return Err(Error::Invariant(
                "encoded route region does not decode to generated code".into(),
            ));
        }
        result.patch_address(route_va, &decoded);
    }
    layout.verify_routes(
        &result,
        selected,
        &image.moved,
        &image.lengths,
        &image.entries,
        seed,
    )?;
    if let Some(placed) = &vm_image {
        vm::verify(&result, placed, &image.entries, selected, seed).map_err(Error::invariant)?;
    }

    let map_bytes = map.map(|_| {
        let mut lines = format!("# seed 0x{seed:x}\n# old_va new_va bytes\n");
        for (&old, &new) in &image.moved {
            let len = image.lengths[&old];
            writeln!(lines, "0x{old:x}\t0x{new:x}\t{len}").unwrap();
        }
        lines.into_bytes()
    });
    publish(
        &output_bytes,
        output,
        input.permissions.clone(),
        map.zip(map_bytes.as_deref()),
    )?;
    let vm_count = selected
        .iter()
        .filter(|item| item.mode() == Mode::Vm)
        .count();
    let strong = selected
        .iter()
        .filter(|item| item.mode() == Mode::Strong)
        .count();
    let layout_count = selected.len() - strong - vm_count;
    if vm_count == 0 {
        writeln!(report,
            "rewrote {strong} strong, {layout_count} layout, {} fragments (seed 0x{seed:x}, {skipped} skipped)",
            image.moved.len()
        ).map_err(|e| e.to_string())?;
    } else {
        writeln!(report,
            "rewrote {vm_count} vm, {strong} strong, {layout_count} layout, {} blocks (seed 0x{seed:x}, {skipped} skipped)",
            image.moved.len()
        ).map_err(|e| e.to_string())?;
    }
    Ok(RewriteOutcome::Complete)
}

mod vm {
    use std::collections::{BTreeMap, BTreeSet};

    use iced_x86::{
        BlockEncoder, BlockEncoderOptions, Decoder, DecoderOptions, FlowControl, Instruction,
        InstructionBlock, Mnemonic, OpKind, Register,
    };
    use lief::elf::{self, relocation};
    use lief::generic::{Relocation as _, Section as _, Symbol as _};

    use super::{
        ENDBR64, Error, Exit, FrameRegion, FrameRegisterRule, Function, Mode, Result, Selected,
        UnwindRule, align_up, condition_opcode, function_seed, in_range, permute_all,
        register_number, rel32, sleb, uleb, whole_simd_state,
    };
    mod stack {
        use std::collections::{BTreeMap, BTreeSet, VecDeque};

        use iced_x86::{
            FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
        };

        use super::VM_FRAME_SHIFT;
        use crate::{Error, Exit, Function, Result, register_number};

        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct State {
            depth: i64,
            rbp: Option<i64>,
            aliases: [Option<i64>; 16],
        }

        fn stack_address(state: &State, register: Register) -> Option<i64> {
            match register {
                Register::RSP => Some(state.depth),
                Register::RBP if state.rbp.is_some() => state.rbp,
                _ => register_number(register.full_register())
                    .ok()
                    .and_then(|index| state.aliases[index as usize]),
            }
        }

        #[derive(Clone, Copy)]
        pub(super) struct Site {
            pub before: i64,
            pub after: i64,
            pub displacement: i64,
        }

        pub(super) struct StackPlan {
            pub sites: BTreeMap<u64, Site>,
            pub max_depth: u64,
            pub reachable: BTreeSet<u64>,
        }

        fn stack_effect(instruction: &Instruction, state: &mut State) -> Result<()> {
            let name = instruction.mnemonic();
            let destination = instruction.op0_register();
            let source = instruction.op1_register();
            let old = state.depth;
            if name == Mnemonic::Lea
                && destination == Register::RBP
                && matches!(instruction.memory_base(), Register::RSP | Register::RBP)
            {
                return Err(format!("untracked frame pointer at 0x{:x}", instruction.ip()).into());
            }
            if state.rbp.is_some()
                && destination.full_register() == Register::RBP
                && !(name == Mnemonic::Mov && source == Register::RSP)
                && name != Mnemonic::Pop
                && name != Mnemonic::Leave
            {
                let mut info = InstructionInfoFactory::new();
                if info.info(instruction).used_registers().iter().any(|used| {
                    used.register().full_register() == Register::RBP
                        && matches!(
                            used.access(),
                            OpAccess::Write
                                | OpAccess::ReadWrite
                                | OpAccess::CondWrite
                                | OpAccess::ReadCondWrite
                        )
                }) {
                    return Err(
                        format!("modified frame pointer at 0x{:x}", instruction.ip()).into(),
                    );
                }
            }
            match name {
                Mnemonic::Push | Mnemonic::Pushfq => {
                    state.depth = state
                        .depth
                        .checked_add(i64::from(instruction.stack_pointer_increment()))
                        .ok_or("stack offset overflow")?;
                }
                Mnemonic::Pop | Mnemonic::Popfq => {
                    if destination == Register::RSP {
                        return Err("POP RSP has a dynamic stack result".into());
                    }
                    state.depth = state
                        .depth
                        .checked_add(i64::from(instruction.stack_pointer_increment()))
                        .ok_or("stack offset overflow")?;
                }
                Mnemonic::Leave => {
                    state.depth = state
                        .rbp
                        .ok_or("LEAVE has no known frame pointer")?
                        .checked_add(8)
                        .ok_or("stack offset overflow")?;
                    state.rbp = None;
                }
                Mnemonic::Add | Mnemonic::Sub if destination == Register::RSP => {
                    let immediate = instruction
                        .try_immediate(1)
                        .map_err(|_| "dynamic stack arithmetic")?
                        as i64;
                    state.depth = if name == Mnemonic::Sub {
                        state.depth.checked_sub(immediate)
                    } else {
                        state.depth.checked_add(immediate)
                    }
                    .ok_or("stack offset overflow")?;
                }
                Mnemonic::Lea
                    if destination == Register::RSP
                        && instruction.memory_base() == Register::RSP
                        && instruction.memory_index() == Register::None =>
                {
                    state.depth = state
                        .depth
                        .checked_add(instruction.memory_displacement64() as i64)
                        .ok_or("stack offset overflow")?;
                }
                Mnemonic::Mov
                    if destination == Register::RSP
                        && instruction.op1_register() == Register::RBP =>
                {
                    state.depth = state
                        .rbp
                        .ok_or("RSP restored from an unknown frame pointer")?;
                }
                _ if matches!(
                    instruction.flow_control(),
                    FlowControl::Call | FlowControl::IndirectCall | FlowControl::Return
                ) => {}
                _ => {
                    let mut info = InstructionInfoFactory::new();
                    if info.info(instruction).used_registers().iter().any(|used| {
                        used.register().full_register() == Register::RSP
                            && matches!(
                                used.access(),
                                OpAccess::Write
                                    | OpAccess::ReadWrite
                                    | OpAccess::CondWrite
                                    | OpAccess::ReadCondWrite
                            )
                    }) {
                        return Err(format!("dynamic RSP write at 0x{:x}", instruction.ip()).into());
                    }
                }
            }
            if state.depth > 0 {
                return Err("stack pointer rose above the entry frame".into());
            }
            if state.depth < -(1 << 26) {
                return Err("VM stack frame exceeds 64 MiB".into());
            }
            if name == Mnemonic::Mov
                && destination == Register::RBP
                && instruction.op1_register() == Register::RSP
            {
                state.rbp = Some(old);
            } else if name == Mnemonic::Pop && destination == Register::RBP {
                state.rbp = None;
            } else if destination == Register::RBP && instruction.op0_kind() == OpKind::Register {
                let mut info = InstructionInfoFactory::new();
                if info.info(instruction).used_registers().iter().any(|used| {
                    used.register().full_register() == Register::RBP
                        && matches!(
                            used.access(),
                            OpAccess::Write
                                | OpAccess::ReadWrite
                                | OpAccess::CondWrite
                                | OpAccess::ReadCondWrite
                        )
                }) {
                    state.rbp = None;
                }
            }
            Ok(())
        }

        fn site(instruction: &Instruction, state: &mut State, deepest: &mut i64) -> Result<Site> {
            let previous = *state;
            let before = state.depth;
            let mut displacement = 0;
            let mut address_alias = None;
            if instruction.op_count() != 0
                && (0..instruction.op_count()).any(|op| instruction.op_kind(op) == OpKind::Memory)
            {
                let base_register = instruction.memory_base();
                if base_register.size() != 8
                    && stack_address(state, base_register.full_register()).is_some()
                {
                    return Err("address-size override on stack pointer".into());
                }
                let alias = stack_address(state, base_register)
                    .map(|base| {
                        if instruction.mnemonic() == Mnemonic::Pop
                            && instruction.op0_kind() == OpKind::Memory
                            && base_register == Register::RSP
                        {
                            base.checked_add(i64::from(instruction.stack_pointer_increment()))
                                .ok_or("stack address overflow")
                        } else {
                            Ok(base)
                        }
                    })
                    .transpose()?;
                if stack_address(state, instruction.memory_index()).is_some() {
                    return Err("stack pointer used as an address index".into());
                }
                if let Some(base) = alias {
                    if instruction.memory_index() != Register::None
                        || instruction.segment_prefix() != Register::None
                    {
                        return Err(format!(
                            "unresolved stack address at 0x{:x}",
                            instruction.ip()
                        )
                        .into());
                    }
                    let address = base
                        .checked_add(instruction.memory_displacement64() as i64)
                        .ok_or("stack address overflow")?;
                    let width = i64::try_from(instruction.memory_size().size())
                        .map_err(|_| "stack width overflow")?;
                    if address < 0 && address.checked_add(width).is_none_or(|end| end > 0) {
                        return Err(format!(
                            "stack operand crosses entry at 0x{:x}",
                            instruction.ip()
                        )
                        .into());
                    }
                    let canonical = base_register == Register::RSP
                        || (base_register == Register::RBP && state.rbp.is_some());
                    if canonical {
                        if address >= 0 {
                            displacement = VM_FRAME_SHIFT as i64;
                        }
                    } else if (base < 0) != (address < 0) {
                        return Err("stack alias crosses the entry frame".into());
                    }
                    if address < 0 {
                        *deepest = (*deepest).min(address);
                    }
                    if instruction.mnemonic() == Mnemonic::Lea {
                        if instruction.op0_register().size() != 8 {
                            return Err("truncated stack pointer alias".into());
                        }
                        address_alias = Some(address);
                    }
                }
            }
            let destination = instruction.op0_register();
            let mut result_alias = address_alias;
            let mut info_factory = InstructionInfoFactory::new();
            let info = info_factory.info(instruction);
            for used in info.used_registers() {
                if stack_address(&previous, used.register().full_register()).is_some()
                    && (matches!(used.access(), OpAccess::CondWrite | OpAccess::ReadCondWrite)
                        || (used.register().size() < 4
                            && matches!(used.access(), OpAccess::Write | OpAccess::ReadWrite)))
                {
                    return Err("partial or conditional stack alias write".into());
                }
            }
            for operand in 0..instruction.op_count() {
                if instruction.op_kind(operand) != OpKind::Register {
                    continue;
                }
                let register = instruction.op_register(operand);
                let Some(offset) = stack_address(&previous, register.full_register()) else {
                    continue;
                };
                if !matches!(
                    info.op_access(operand),
                    OpAccess::Read
                        | OpAccess::ReadWrite
                        | OpAccess::CondRead
                        | OpAccess::ReadCondWrite
                ) {
                    continue;
                }
                if register.full_register() == Register::RSP
                    || (register.full_register() == Register::RBP && previous.rbp.is_some())
                {
                    let frame_move = instruction.mnemonic() == Mnemonic::Mov
                        && operand == 1
                        && matches!(
                            (destination, register),
                            (Register::RBP, Register::RSP) | (Register::RSP, Register::RBP)
                        );
                    let stack_adjustment =
                        matches!(instruction.mnemonic(), Mnemonic::Add | Mnemonic::Sub)
                            && operand == 0
                            && register == Register::RSP;
                    if !frame_move && !stack_adjustment {
                        return Err(format!(
                            "untracked stack pointer alias at 0x{:x}",
                            instruction.ip()
                        )
                        .into());
                    }
                    continue;
                }
                match instruction.mnemonic() {
                    Mnemonic::Mov
                        if operand == 1 && destination.size() == 8 && register.size() == 8 =>
                    {
                        result_alias = Some(offset);
                    }
                    Mnemonic::Add | Mnemonic::Sub if operand == 0 && destination.size() == 8 => {
                        let immediate = instruction
                            .try_immediate(1)
                            .map_err(|_| "unresolved stack alias arithmetic")?
                            as i64;
                        let adjusted = if instruction.mnemonic() == Mnemonic::Add {
                            offset.checked_add(immediate)
                        } else {
                            offset.checked_sub(immediate)
                        }
                        .ok_or("stack alias overflow")?;
                        if (offset < 0) != (adjusted < 0) {
                            return Err("stack alias crosses the entry frame".into());
                        }
                        result_alias = Some(adjusted);
                    }
                    Mnemonic::Xor | Mnemonic::Sub
                        if instruction.op0_register() == instruction.op1_register() => {}
                    _ => return Err("unresolved stack pointer alias use".into()),
                }
            }
            if instruction.op_count() != 0
                && instruction.op0_kind() != OpKind::Memory
                && !matches!(
                    instruction.mnemonic(),
                    Mnemonic::Push
                        | Mnemonic::Pop
                        | Mnemonic::Pushfq
                        | Mnemonic::Popfq
                        | Mnemonic::Leave
                        | Mnemonic::Ret
                )
                && instruction.flow_control() != FlowControl::Call
                && instruction.flow_control() != FlowControl::IndirectCall
            {
                for memory in info.used_memory() {
                    if instruction.op_kinds().any(|kind| kind == OpKind::Memory) {
                        break;
                    }
                    if stack_address(state, memory.base()).is_some()
                        || stack_address(state, memory.index()).is_some()
                    {
                        return Err("implicit stack alias memory access".into());
                    }
                }
            }
            stack_effect(instruction, state)?;
            for used in info.used_registers() {
                if matches!(
                    used.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                ) && let Ok(index) = register_number(used.register().full_register())
                {
                    state.aliases[index as usize] = None;
                }
            }
            if let Some(offset) = result_alias
                && let Ok(index) = register_number(destination.full_register())
                && destination != Register::RSP
            {
                state.aliases[index as usize] = Some(offset);
            }
            if matches!(
                instruction.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                for index in [0, 1, 2, 6, 7, 8, 9, 10, 11] {
                    state.aliases[index] = None;
                }
            }
            *deepest = (*deepest).min(state.depth);
            Ok(Site {
                before,
                after: state.depth,
                displacement,
            })
        }

        pub(super) fn plan(function: &Function, noreturn: &BTreeSet<u64>) -> Result<StackPlan> {
            let initial = State {
                depth: 0,
                rbp: None,
                aliases: [None; 16],
            };
            let mut pending = VecDeque::new();
            let mut states = BTreeMap::new();
            for label in std::iter::once(function.start)
                .chain(function.entries.iter().map(|entry| entry.label))
            {
                if states.insert(label, initial).is_none() {
                    pending.push_back(label);
                }
            }
            let mut sites = BTreeMap::new();
            let mut deepest = 0;
            while let Some(start) = pending.pop_front() {
                let block = function
                    .blocks
                    .iter()
                    .find(|block| block.old == start)
                    .ok_or_else(|| Error::Invariant("VM stack block missing".into()))?;
                let mut state = states[&start];
                for instruction in &block.body {
                    let at = site(instruction, &mut state, &mut deepest)?;
                    if let Some(old) = sites.insert(instruction.ip(), at)
                        && (old.before != at.before
                            || old.after != at.after
                            || old.displacement != at.displacement)
                    {
                        return Err("inconsistent stack state at instruction".into());
                    }
                }
                let successors: Vec<_> = match block.exit {
                    Exit::Branch {
                        target,
                        fallthrough,
                        ..
                    } => vec![target, fallthrough],
                    Exit::Jump(target)
                        if !crate::in_range(target, function.start, function.end) =>
                    {
                        if state.depth != 0 {
                            return Err("VM tail jump has an unbalanced stack".into());
                        }
                        Vec::new()
                    }
                    Exit::Fallthrough(target)
                        if target == function.end && noreturn.contains(&block.old) =>
                    {
                        Vec::new()
                    }
                    Exit::Jump(target) | Exit::Fallthrough(target) => vec![target],
                    Exit::Return => {
                        if state.depth != 0 {
                            return Err("return has an unbalanced stack".into());
                        }
                        Vec::new()
                    }
                    Exit::Table(_) | Exit::Dispatch(_) => {
                        return Err("computed jump requires route mode".into());
                    }
                };
                for target in successors {
                    if target < function.start || target >= function.end {
                        return Err("control flow leaves VM function".into());
                    }
                    match states.get(&target) {
                        Some(previous) if *previous != state => {
                            return Err(format!("stack state differs at 0x{target:x}").into());
                        }
                        Some(_) => {}
                        None => {
                            states.insert(target, state);
                            pending.push_back(target);
                        }
                    }
                }
            }
            for (index, block) in function.blocks.iter().enumerate() {
                if states.contains_key(&block.old) {
                    continue;
                }
                let end = function
                    .blocks
                    .get(index + 1)
                    .map_or(function.end, |next| next.old);
                let padding = !block.body.is_empty()
                    && block.body.iter().all(|ins| ins.mnemonic() == Mnemonic::Nop)
                    && matches!(block.exit, Exit::Fallthrough(_))
                    && !function
                        .entries
                        .iter()
                        .any(|entry| entry.label >= block.old && entry.label < end)
                    && !function.unwind.as_ref().is_some_and(|rows| {
                        rows.iter()
                            .any(|(address, _)| *address >= block.old && *address < end)
                    });
                if !padding {
                    return Err("unreachable VM block has no stack state".into());
                }
            }
            let reachable_sites: usize = function
                .blocks
                .iter()
                .filter(|block| states.contains_key(&block.old))
                .map(|block| block.body.len())
                .sum();
            if sites.len() != reachable_sites {
                return Err("inconsistent VM instruction sites".into());
            }
            let max_depth = u64::try_from(deepest.checked_neg().ok_or("stack depth overflow")?)
                .map_err(|_| "stack depth overflow")?;
            Ok(StackPlan {
                sites,
                max_depth,
                reachable: states.keys().copied().collect(),
            })
        }

        #[cfg(test)]
        mod tests {
            use std::collections::BTreeSet;

            use iced_x86::{ConditionCode, Decoder, DecoderOptions};

            use super::{State, site};
            use crate::vm::VM_FRAME_SHIFT;
            use crate::{Block, EntryPatch, Exit, Function, UnwindRule};

            fn plan(function: &Function) -> crate::Result<super::StackPlan> {
                super::plan(function, &BTreeSet::new())
            }

            #[test]
            fn terminal_noreturn_call_needs_proof() {
                let mut decoder =
                    Decoder::with_ip(64, &[0x50, 0xe8, 0, 0, 0, 0], 0x1000, DecoderOptions::NONE);
                let function = Function {
                    start: 0x1000,
                    end: 0x1006,
                    bytes: Vec::new(),
                    entries: Vec::new(),
                    blocks: vec![Block {
                        old: 0x1000,
                        body: vec![decoder.decode(), decoder.decode()],
                        exit: Exit::Fallthrough(0x1006),
                        len: 6,
                    }],
                    tables: Vec::new(),
                    dispatches: Vec::new(),
                    fixed_targets: Vec::new(),
                    fixed_slots: Vec::new(),
                    unwind: None,
                };
                assert!(plan(&function).is_err());
                let noreturn = BTreeSet::from([0x1000]);
                assert!(super::plan(&function, &noreturn).is_ok());
            }

            #[test]
            fn excludes_only_unreferenced_nop_padding() {
                let mut decoder = Decoder::with_ip(
                    64,
                    &[0x90, 0x0f, 0x1f, 0x40, 0x00, 0xc3],
                    0x1001,
                    DecoderOptions::NONE,
                );
                let nop = decoder.decode();
                let wide_nop = decoder.decode();
                let ret = decoder.decode();
                let mut function = Function {
                    start: 0x1000,
                    end: 0x1007,
                    bytes: Vec::new(),
                    entries: Vec::new(),
                    blocks: vec![
                        Block {
                            old: 0x1000,
                            body: Vec::new(),
                            exit: Exit::Jump(0x1006),
                            len: 5,
                        },
                        Block {
                            old: 0x1001,
                            body: vec![nop, wide_nop],
                            exit: Exit::Fallthrough(0x1006),
                            len: 5,
                        },
                        Block {
                            old: 0x1006,
                            body: vec![ret],
                            exit: Exit::Return,
                            len: 1,
                        },
                    ],
                    tables: Vec::new(),
                    dispatches: Vec::new(),
                    fixed_targets: Vec::new(),
                    fixed_slots: Vec::new(),
                    unwind: None,
                };
                assert_eq!(plan(&function).unwrap().reachable.len(), 2);
                function.blocks[0].exit = Exit::Jump(0x1001);
                assert!(plan(&function).unwrap().reachable.contains(&0x1001));
                function.blocks[0].exit = Exit::Jump(0x1006);
                function.entries.push(EntryPatch {
                    label: 0x1001,
                    window: None,
                    sources: Vec::new(),
                });
                assert!(plan(&function).unwrap().reachable.contains(&0x1001));
                function.entries.clear();
                function.unwind = Some(vec![(
                    0x1001,
                    UnwindRule {
                        cfa_register: 7,
                        cfa_offset: 8,
                        cfa_expression: None,
                        registers: Default::default(),
                    },
                )]);
                assert!(plan(&function).is_err());
                function.unwind = None;
                let mut decoder = Decoder::with_ip(64, &[0x50], 0x1001, DecoderOptions::NONE);
                function.blocks[1].body[0] = decoder.decode();
                assert!(plan(&function).is_err());
                function.blocks[1].body[0] = nop;
                let mut decoder = Decoder::with_ip(64, &[0xc3], 0x1000, DecoderOptions::NONE);
                function.blocks[0].body.push(decoder.decode());
                function.blocks[0].exit = Exit::Return;
                function.blocks.pop();
                function.end = 0x1006;
                function.blocks[1].exit = Exit::Fallthrough(0x1006);
                assert_eq!(plan(&function).unwrap().reachable.len(), 1);
            }

            #[test]
            fn tracks_frame_pointer_and_entry_argument() {
                let code = [
                    0x55, // push rbp
                    0x48, 0x89, 0xe5, // mov rbp, rsp
                    0x48, 0x83, 0xec, 0x20, // sub rsp, 32
                    0x48, 0x8d, 0x45, 0x10, // lea rax, [rbp + 16]
                    0xc9, // leave
                    0xc3, // ret
                ];
                let mut decoder = Decoder::with_ip(64, &code, 0x1000, DecoderOptions::NONE);
                let mut state = State {
                    depth: 0,
                    rbp: None,
                    aliases: [None; 16],
                };
                let mut deepest = 0;
                let sites: Vec<_> = (0..6)
                    .map(|_| site(&decoder.decode(), &mut state, &mut deepest).unwrap())
                    .collect();
                assert_eq!(sites[3].displacement, VM_FRAME_SHIFT as i64);
                assert_eq!(sites[3].before, -40);
                assert_eq!(state.depth, 0);
                assert_eq!(deepest, -40);
            }

            #[test]
            fn pop_rsp_memory_uses_post_increment_address() {
                for (bytes, displacement) in [
                    (&[0x8f, 0x04, 0x24][..], VM_FRAME_SHIFT as i64),
                    (&[0x8f, 0x44, 0x24, 0xf8][..], 0),
                ] {
                    let mut decoder = Decoder::with_ip(64, bytes, 0x1000, DecoderOptions::NONE);
                    let mut state = State {
                        depth: -8,
                        rbp: None,
                        aliases: [None; 16],
                    };
                    let site = site(&decoder.decode(), &mut state, &mut -8).unwrap();
                    assert_eq!(
                        (site.before, site.after, site.displacement),
                        (-8, 0, displacement)
                    );
                }
                let mut decoder =
                    Decoder::with_ip(64, &[0x8f, 0x44, 0x24, 0xfc], 0x1000, DecoderOptions::NONE);
                let mut state = State {
                    depth: -8,
                    rbp: None,
                    aliases: [None; 16],
                };
                assert!(site(&decoder.decode(), &mut state, &mut -8).is_err());
            }

            #[test]
            fn rejects_untracked_stack_pointer() {
                let code = [0x48, 0x89, 0xc4]; // mov rsp, rax
                let mut decoder = Decoder::with_ip(64, &code, 0x2000, DecoderOptions::NONE);
                let mut state = State {
                    depth: 0,
                    rbp: None,
                    aliases: [None; 16],
                };
                assert!(site(&decoder.decode(), &mut state, &mut 0).is_err());
            }

            #[test]
            fn tracks_derived_rbp_without_rebasing_it() {
                for offset in [-24, 8] {
                    let mut state = State {
                        depth: -24,
                        rbp: None,
                        aliases: [None; 16],
                    };
                    state.aliases[0] = Some(offset);
                    let mut decoder = Decoder::with_ip(
                        64,
                        &[0x48, 0x89, 0xc5, 0x48, 0x8b, 0x45, 0],
                        0x2000,
                        DecoderOptions::NONE,
                    );
                    site(&decoder.decode(), &mut state, &mut 0).unwrap();
                    assert_eq!(state.rbp, None);
                    assert_eq!(state.aliases[5], Some(offset));
                    assert_eq!(
                        site(&decoder.decode(), &mut state, &mut 0)
                            .unwrap()
                            .displacement,
                        0
                    );
                    let mut decoder =
                        Decoder::with_ip(64, &[0x48, 0x89, 0xeb], 0x2007, DecoderOptions::NONE); // mov rbx, rbp
                    site(&decoder.decode(), &mut state, &mut 0).unwrap();
                    assert_eq!(state.aliases[3], Some(offset));
                }
                let mut state = State {
                    depth: -24,
                    rbp: None,
                    aliases: [None; 16],
                };
                state.aliases[0] = Some(-24);
                let mut decoder = Decoder::with_ip(
                    64,
                    &[0x48, 0x89, 0xc5, 0x48, 0x8b, 0x45, 32],
                    0x2000,
                    DecoderOptions::NONE,
                );
                site(&decoder.decode(), &mut state, &mut 0).unwrap();
                assert_eq!(
                    site(&decoder.decode(), &mut state, &mut 0)
                        .err()
                        .unwrap()
                        .to_string(),
                    "stack alias crosses the entry frame"
                );
            }

            #[test]
            fn rejects_partial_and_conditional_alias_updates() {
                for canonical in [false, true] {
                    for code in [
                        &[0x66, 0xbd, 0, 0][..],   // mov bp, 0
                        &[0x40, 0xb5, 0],          // mov bpl, 0
                        &[0x48, 0x0f, 0x44, 0xe9], // cmove rbp, rcx
                        &[0x0f, 0x44, 0xe9],       // cmove ebp, ecx
                    ] {
                        let mut state = State {
                            depth: -24,
                            rbp: canonical.then_some(-8),
                            aliases: [None; 16],
                        };
                        state.aliases[5] = Some(-24);
                        let mut decoder = Decoder::with_ip(64, code, 0x2000, DecoderOptions::NONE);
                        assert!(
                            site(&decoder.decode(), &mut state, &mut 0).is_err(),
                            "{code:x?}"
                        );
                    }
                }
                let mut state = State {
                    depth: -24,
                    rbp: None,
                    aliases: [None; 16],
                };
                let mut decoder =
                    Decoder::with_ip(64, &[0x8d, 0x04, 0x24], 0x2000, DecoderOptions::NONE);
                assert!(site(&decoder.decode(), &mut state, &mut 0).is_err());
                state.aliases[5] = Some(-24);
                let mut decoder =
                    Decoder::with_ip(64, &[0xbd, 0, 0, 0, 0], 0x2000, DecoderOptions::NONE);
                site(&decoder.decode(), &mut state, &mut 0).unwrap();
                assert_eq!(state.aliases[5], None);
                state.rbp = Some(-8);
                let mut decoder =
                    Decoder::with_ip(64, &[0xbd, 0, 0, 0, 0], 0x2000, DecoderOptions::NONE);
                assert!(site(&decoder.decode(), &mut state, &mut 0).is_err());
            }

            #[test]
            fn uses_operand_size_for_push_and_pop() {
                let code = [0x66, 0x50, 0x66, 0x58]; // push ax; pop ax
                let mut decoder = Decoder::with_ip(64, &code, 0x3000, DecoderOptions::NONE);
                let mut state = State {
                    depth: 0,
                    rbp: None,
                    aliases: [None; 16],
                };
                let mut deepest = 0;
                let pushed = site(&decoder.decode(), &mut state, &mut deepest).unwrap();
                let popped = site(&decoder.decode(), &mut state, &mut deepest).unwrap();
                assert_eq!(pushed.after, -2);
                assert_eq!(popped.after, 0);
            }

            #[test]
            fn rejects_stack_pointer_alias() {
                for code in [
                    &[0x48, 0x89, 0xe0][..],   // mov rax,rsp
                    &[0x48, 0x89, 0x24, 0x24], // mov [rsp],rsp
                    &[0x54],                   // push rsp
                    &[0x89, 0xe0],             // mov eax,esp
                ] {
                    let mut decoder = Decoder::with_ip(64, code, 0x4000, DecoderOptions::NONE);
                    let mut state = State {
                        depth: 0,
                        rbp: None,
                        aliases: [None; 16],
                    };
                    assert!(site(&decoder.decode(), &mut state, &mut 0).is_err());
                }
            }

            #[test]
            fn follows_local_aliases_and_rejects_cross_frame_access() {
                // sub rsp,32; lea rax,[rsp+8]; mov rcx,rax; mov rdx,[rcx]; mov rdx,[rcx+32]
                let bytes = [
                    0x48, 0x83, 0xec, 0x20, 0x48, 0x8d, 0x44, 0x24, 0x08, 0x48, 0x89, 0xc1, 0x48,
                    0x8b, 0x11, 0x48, 0x8b, 0x51, 0x20,
                ];
                let mut decoder = Decoder::with_ip(64, &bytes, 0x1000, DecoderOptions::NONE);
                let mut state = State {
                    depth: 0,
                    rbp: None,
                    aliases: [None; 16],
                };
                let mut deepest = 0;
                for _ in 0..4 {
                    site(&decoder.decode(), &mut state, &mut deepest).unwrap();
                }
                assert_eq!(state.aliases[1], Some(-24));
                assert!(site(&decoder.decode(), &mut state, &mut deepest).is_err());
            }

            #[test]
            fn rejects_truncated_stack_addresses() {
                let mut decoder = Decoder::with_ip(
                    64,
                    &[0x67, 0x48, 0x8b, 0x04, 0x24],
                    0x1000,
                    DecoderOptions::NONE,
                );
                let mut state = State {
                    depth: 0,
                    rbp: None,
                    aliases: [None; 16],
                };
                assert!(site(&decoder.decode(), &mut state, &mut 0).is_err());
            }

            #[test]
            fn joins_require_the_same_stack_provenance() {
                let mut decoder = Decoder::with_ip(
                    64,
                    &[0x48, 0x8d, 0x44, 0x24, 0xf8],
                    0x1010,
                    DecoderOptions::NONE,
                );
                let alias = decoder.decode();
                let mut function = Function {
                    start: 0x1000,
                    end: 0x1040,
                    bytes: Vec::new(),
                    entries: Vec::new(),
                    tables: Vec::new(),
                    dispatches: Vec::new(),
                    fixed_targets: Vec::new(),
                    fixed_slots: Vec::new(),
                    unwind: None,
                    blocks: vec![
                        Block {
                            old: 0x1000,
                            body: Vec::new(),
                            exit: Exit::Branch {
                                target: 0x1010,
                                fallthrough: 0x1020,
                                cc: ConditionCode::e,
                            },
                            len: 0,
                        },
                        Block {
                            old: 0x1010,
                            body: vec![alias],
                            exit: Exit::Jump(0x1030),
                            len: 5,
                        },
                        Block {
                            old: 0x1020,
                            body: Vec::new(),
                            exit: Exit::Jump(0x1030),
                            len: 0,
                        },
                        Block {
                            old: 0x1030,
                            body: Vec::new(),
                            exit: Exit::Return,
                            len: 0,
                        },
                    ],
                };
                assert!(plan(&function).is_err());
                let mut decoder = Decoder::with_ip(
                    64,
                    &[0x48, 0x89, 0xc5, 0x31, 0xc0], // mov rbp, rax; xor eax, eax
                    0x1015,
                    DecoderOptions::NONE,
                );
                function.blocks[1]
                    .body
                    .extend([decoder.decode(), decoder.decode()]);
                assert!(plan(&function).is_err());
                function.blocks[2].body = function.blocks[1].body.clone();
                for instruction in &mut function.blocks[2].body {
                    instruction.set_ip(instruction.ip() + 0x10);
                }
                assert!(plan(&function).is_ok());
                function.blocks[2].body.clear();
                function.blocks[1].body.clear();
                assert!(plan(&function).is_ok());
                function.entries = [0x1000, 0x1020]
                    .into_iter()
                    .map(|label| EntryPatch {
                        label,
                        window: None,
                        sources: Vec::new(),
                    })
                    .collect();
                assert!(plan(&function).is_ok());
                for target in [0xff0, 0x1040, 0x1050] {
                    function.blocks[3].exit = Exit::Fallthrough(target);
                    let error = plan(&function).err().unwrap().eligibility();
                    assert!(matches!(error, crate::Error::Unsupported(_)));
                    assert_eq!(error.to_string(), "control flow leaves VM function");
                }
                function.blocks[3].exit = Exit::Jump(0x1050);
                assert!(plan(&function).is_ok());
                let mut decoder = Decoder::with_ip(64, &[0x50], 0x1030, DecoderOptions::NONE);
                function.blocks[3].body.push(decoder.decode());
                assert_eq!(
                    plan(&function).err().unwrap().to_string(),
                    "VM tail jump has an unbalanced stack"
                );
            }
        }
    }

    include!(concat!(env!("OUT_DIR"), "/vm_runtime_offsets.rs"));
    const RUNTIME: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/vm_runtime.bin"));
    include!(concat!(env!("OUT_DIR"), "/vm_abi.rs"));
    const OP_LEN: usize = VM_OP_LEN;
    const THUNK_LEN: usize = 18;
    const META_LEN: usize = VM_META_LEN;
    const ISLAND_LEN: usize = 128;

    fn frame_depth(depth: u64) -> Result<u64> {
        if depth > 64 * 1024 * 1024 {
            return Err(Error::Unsupported("VM stack frame exceeds 64 MiB".into()));
        }
        let depth = align_up(usize::try_from(depth).map_err(|_| "VM frame overflow")?, 16)?;
        // Guest locals and their red zone precede the interpreter workspace. Include
        // one extra probe page, since the assembly probe may round below its target.
        let allocation = depth
            .checked_add(VM_FRAME_SHIFT)
            .and_then(|n| n.checked_add(128 + VM_HOST_STACK + 4096))
            .ok_or("VM frame allocation overflow")?;
        i32::try_from(allocation).map_err(|_| "VM frame exceeds recovery displacement")?;
        Ok(depth as u64)
    }

    #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
    enum Target {
        None,
        Block(u64),
        Relay(usize),
        Island(usize),
        External(u64),
        Abort,
    }

    #[derive(Clone, Copy)]
    struct Op {
        code: u8,
        width: u8,
        reg: u8,
        dst: u8,
        src: u8,
        base: u8,
        index: u8,
        scale: u8,
        flags: u8,
        value: i64,
        target: Target,
    }

    impl Op {
        fn new(code: u8, width: u8) -> Self {
            Self {
                code,
                width,
                reg: 0,
                dst: 0,
                src: 0,
                base: 255,
                index: 255,
                scale: 1,
                flags: 0,
                value: 0,
                target: Target::None,
            }
        }
    }

    fn encode_metadata(ops: i64, pc: u32, count: u32, codec: i64, depth: u64) -> [u8; META_LEN] {
        let mut bytes = [0; META_LEN];
        bytes[..8].copy_from_slice(&ops.to_le_bytes());
        bytes[8..12].copy_from_slice(&pc.to_le_bytes());
        bytes[12..16].copy_from_slice(&count.to_le_bytes());
        bytes[16..24].copy_from_slice(&codec.to_le_bytes());
        bytes[24..32].copy_from_slice(&depth.to_le_bytes());
        bytes
    }

    fn serialize_op(op: &Op, architecture: Architecture, value: i64, target: i64) -> [u8; OP_LEN] {
        let mut bytes = [0; OP_LEN];
        bytes[..8].copy_from_slice(&match architecture {
            _ if (VM_F_MOV_RR..=VM_F_TEST).contains(&op.code) => [
                op.code, op.width, op.dst, op.src, op.base, op.index, op.scale, op.flags,
            ],
            Architecture::Stack => [
                op.code, op.width, op.reg, op.base, op.index, op.scale, op.flags, 0,
            ],
            Architecture::Register => [
                op.code, op.width, op.dst, op.src, op.base, op.index, op.scale, op.flags,
            ],
        });
        bytes[8..16].copy_from_slice(&value.to_le_bytes());
        bytes[16..24].copy_from_slice(&target.to_le_bytes());
        bytes
    }

    struct Codec {
        key: u64,
        architecture: Architecture,
        variant: u8,
        header: [u8; 8],
        words: [u8; 3],
        rounds: [u8; 6],
    }

    impl Codec {
        fn variant(seed: u64, address: u64) -> u8 {
            (function_seed(seed ^ 0x4cf5ad432745937f, address) & 1) as u8
        }

        fn new(seed: u64, address: u64, architecture: Architecture) -> Self {
            let key = function_seed(seed ^ 0x13198a2e03707344, address);
            let header = permute_all(8, key ^ 0x3c6ef372fe94f82b);
            let words = permute_all(3, key ^ 0xa54ff53a5f1d36f1);
            Self {
                key,
                architecture,
                variant: Self::variant(seed, address),
                header: std::array::from_fn(|i| header[i] as u8),
                words: std::array::from_fn(|i| words[i] as u8),
                rounds: std::array::from_fn(|i| {
                    (function_seed(key ^ 0xbb67ae8584caa73b, i as u64) & 15) as u8
                }),
            }
        }

        fn descriptor(&self, blocks: usize, count: usize) -> Result<[u8; VM_CODEC_LEN]> {
            let blocks = u16::try_from(blocks).map_err(|_| "VM block count exceeds limit")?;
            let table = count
                .checked_mul(OP_LEN)
                .and_then(|size| u32::try_from(size).ok())
                .ok_or("VM dispatch table offset exceeds limit")?;
            let mut bytes = [0; VM_CODEC_LEN];
            bytes[..8].copy_from_slice(&self.key.to_le_bytes());
            bytes[VM_CODEC_ARCH] = self.architecture as u8;
            bytes[VM_CODEC_VARIANT] = self.variant;
            bytes[VM_CODEC_BLOCKS..VM_CODEC_BLOCKS + 2].copy_from_slice(&blocks.to_le_bytes());
            bytes[VM_CODEC_TABLE..VM_CODEC_TABLE + 4].copy_from_slice(&table.to_le_bytes());
            Ok(bytes)
        }

        fn valid_opcode(&self, code: u8) -> bool {
            (match self.architecture {
                Architecture::Stack => (VM_PUSH_REG..=VM_SHIFT).contains(&code),
                Architecture::Register => (VM_R_READ_REG..=VM_R_SHIFT).contains(&code),
            }) || (VM_F_MOV_RR..=VM_F_TEST).contains(&code)
        }

        fn round(value: u8, key: u8) -> u8 {
            ((5 * u16::from(value) + u16::from(key)) as u8 ^ ((value << 1) | (value >> 3))) & 15
        }

        fn opcode(&self, code: u8, inverse: bool) -> u8 {
            let (mut left, mut right) = (code >> 4, code & 15);
            if inverse {
                for &key in self.rounds.iter().rev() {
                    (left, right) = (right ^ Self::round(left, key), left);
                }
            } else {
                for &key in &self.rounds {
                    (left, right) = (right, left ^ Self::round(right, key));
                }
            }
            left << 4 | right
        }

        fn offset(&self, word: usize, byte: usize) -> usize {
            self.words[word] as usize * 8
                + if word == 0 {
                    self.header[byte] as usize
                } else {
                    byte
                }
        }

        fn encode_record(&self, mut bytes: [u8; OP_LEN], pc: usize) -> Result<[u8; OP_LEN]> {
            if !self.valid_opcode(bytes[0]) {
                return Err(Error::Invariant(
                    "opcode does not belong to VM architecture".into(),
                ));
            }
            bytes[0] = self.opcode(bytes[0], false);
            let mut wire = [0; OP_LEN];
            for word in 0..3 {
                for byte in 0..8 {
                    wire[self.offset(word, byte)] = bytes[word * 8 + byte];
                }
            }
            mask_record(&mut wire, self.key, pc);
            Ok(wire)
        }

        fn decode_record(&self, record: &[u8], pc: usize) -> Result<[u8; OP_LEN]> {
            let mut wire: [u8; OP_LEN] = record.try_into().map_err(|_| "truncated VM record")?;
            mask_record(&mut wire, self.key, pc);
            let mut bytes = [0; OP_LEN];
            for word in 0..3 {
                for byte in 0..8 {
                    bytes[word * 8 + byte] = wire[self.offset(word, byte)];
                }
            }
            bytes[0] = self.opcode(bytes[0], true);
            if !self.valid_opcode(bytes[0]) {
                return Err("unassigned VM opcode".into());
            }
            Ok(bytes)
        }
    }

    pub(super) fn interpreter_variant(seed: u64, address: u64) -> u8 {
        Codec::variant(seed, address)
    }

    fn mask_record(bytes: &mut [u8; OP_LEN], key: u64, pc: usize) {
        for (word, chunk) in bytes.chunks_exact_mut(8).enumerate() {
            let mask = function_seed(
                key ^ (word as u64).wrapping_mul(0x9e3779b97f4a7c15),
                pc as u64,
            );
            let value = u64::from_le_bytes(chunk.try_into().unwrap()) ^ mask;
            chunk.copy_from_slice(&value.to_le_bytes());
        }
    }

    struct VmBlock {
        old: u64,
        ops: Vec<Op>,
    }

    struct NativeIsland {
        instruction: Instruction,
        stack: stack::Site,
    }

    pub(super) struct VmPlan {
        pub architecture: Architecture,
        blocks: Vec<VmBlock>,
        relays: Vec<Vec<Op>>,
        islands: Vec<NativeIsland>,
        op_count: usize,
        max_depth: u64,
    }

    const DISPATCH_ORDER_SALT: u64 = 0x5be0cd19137e2179;
    const DISPATCH_MASK_SALT: u64 = 0x1f83d9abfb41bd6b;
    const RELAY_SITE_SALT: u64 = 0x243f6a8885a308d3;
    const RELAY_CONDITION_SALT: u64 = 0x13198a2e03707344;

    struct Dispatch {
        tokens: BTreeMap<Target, usize>,
        bytes: Vec<u8>,
    }

    fn dispatch(
        plan: &VmPlan,
        pc: &BTreeMap<u64, usize>,
        relay_pc: &[usize],
        codec: &Codec,
    ) -> Result<Dispatch> {
        let entries = plan.blocks.len() + plan.relays.len();
        if plan.blocks.is_empty()
            || entries > u16::MAX as usize
            || relay_pc.len() != plan.relays.len()
        {
            return Err("VM block count exceeds limit".into());
        }
        let order = permute_all(entries, codec.key ^ DISPATCH_ORDER_SALT);
        let mut tokens = BTreeMap::new();
        let mut bytes = Vec::with_capacity(entries * 4);
        for (token, index) in order.into_iter().enumerate() {
            let (label, target) = if index < plan.blocks.len() {
                let old = plan.blocks[index].old;
                (
                    Target::Block(old),
                    *pc.get(&old)
                        .ok_or_else(|| Error::Invariant("VM dispatch target missing".into()))?,
                )
            } else {
                let relay = index - plan.blocks.len();
                (Target::Relay(relay), relay_pc[relay])
            };
            if target >= plan.op_count || tokens.insert(label, token).is_some() {
                return Err(Error::Invariant("invalid VM dispatch target".into()));
            }
            let target = u32::try_from(target).map_err(|_| "VM dispatch target exceeds limit")?;
            let mask = function_seed(codec.key ^ DISPATCH_MASK_SALT, token as u64) as u32;
            bytes.extend_from_slice(&(target ^ mask).to_le_bytes());
        }
        Ok(Dispatch { tokens, bytes })
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    #[repr(u8)]
    pub(super) enum Architecture {
        Stack = VM_ARCH_STACK,
        Register = VM_ARCH_REGISTER,
    }

    impl Architecture {
        fn select(seed: u64, address: u64) -> Self {
            if function_seed(seed ^ 0x8c3c010cb4754c9d, address) & 1 == 0 {
                Self::Stack
            } else {
                Self::Register
            }
        }

        pub fn label(self) -> &'static str {
            match self {
                Self::Stack => " arch=stack",
                Self::Register => " arch=register",
            }
        }
    }

    impl VmPlan {
        pub(super) fn block_count(&self) -> usize {
            self.blocks.len()
        }

        pub(super) fn has_block(&self, address: u64) -> bool {
            self.blocks.iter().any(|block| block.old == address)
        }

        pub fn choose_architecture(&mut self, seed: u64, address: u64) -> Result<()> {
            self.architecture = Architecture::select(seed, address);
            if self.architecture == Architecture::Register {
                let registers = permute_all(32, function_seed(seed ^ 0x47b5481dbefa4fa4, address));
                for block in &mut self.blocks {
                    register_ops(&mut block.ops, &registers)?;
                }
            }
            self.add_relays(seed, address);
            Ok(())
        }

        fn add_relays(&mut self, seed: u64, address: u64) {
            let (jmp, jcc) = match self.architecture {
                Architecture::Stack => (VM_JMP, VM_JCC),
                Architecture::Register => (VM_R_JMP, VM_R_JCC),
            };
            let sites: Vec<_> = self
                .blocks
                .iter()
                .enumerate()
                .filter_map(|(index, block)| match block.ops.last() {
                    Some(op) if op.code == jmp => match op.target {
                        Target::Block(target) => Some((index, target)),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            let limit = 2
                .min((65535 - self.op_count) / 4)
                .min((u16::MAX as usize - self.blocks.len()) / 2);
            let order = permute_all(sites.len(), function_seed(seed ^ RELAY_SITE_SALT, address));
            for site in order.into_iter().take(limit) {
                let (index, target) = sites[site];
                let state = function_seed(seed ^ RELAY_CONDITION_SALT, self.blocks[index].old);
                let first = (state & 15) as u8;
                let mut second = ((state >> 4) & 15) as u8;
                if second == first || second == (first ^ 1) {
                    second = (first + 2) & 15;
                }
                let a = self.relays.len();
                let mut branch = Op::new(jcc, 0);
                branch.flags = first;
                branch.target = Target::Relay(a);
                *self.blocks[index].ops.last_mut().unwrap() = branch;
                let mut jump = Op::new(jmp, 0);
                jump.target = Target::Relay(a + 1);
                self.blocks[index].ops.push(jump);
                jump.target = Target::Block(target);
                self.relays.push(vec![jump]);
                let mut branch = Op::new(jcc, 0);
                branch.flags = second;
                branch.target = Target::Block(target);
                self.relays.push(vec![branch, jump]);
                self.op_count += 4;
            }
        }
    }

    // Lowering produces balanced expressions within each block. Assign their values
    // to explicit temporaries; no operand stack is needed by the register interpreter.
    fn register_ops(ops: &mut [Op], registers: &[usize]) -> Result<()> {
        let invalid =
            || Error::Invariant("unbalanced VM expression during register conversion".into());
        let mut depth = 0usize;
        for op in ops {
            op.code = match op.code {
                VM_PUSH_REG | VM_PUSH_IMM | VM_PUSH_MEM | VM_LEA | VM_PUSH_CC => {
                    op.dst = *registers.get(depth).ok_or_else(invalid)? as u8;
                    depth += 1;
                    match op.code {
                        VM_PUSH_REG => {
                            op.src = op.reg;
                            VM_R_READ_REG
                        }
                        VM_PUSH_IMM => VM_R_IMM,
                        VM_PUSH_MEM => VM_R_LOAD,
                        VM_LEA => VM_R_ADDR,
                        _ => VM_R_CC,
                    }
                }
                VM_POP_REG | VM_POP_MEM => {
                    depth = depth.checked_sub(1).ok_or_else(invalid)?;
                    op.src = registers[depth] as u8;
                    if op.code == VM_POP_REG {
                        op.dst = op.reg;
                        VM_R_WRITE_REG
                    } else {
                        VM_R_STORE
                    }
                }
                VM_CMOV_REG => {
                    depth = depth.checked_sub(1).ok_or_else(invalid)?;
                    op.src = registers[depth] as u8;
                    op.dst = op.reg;
                    VM_R_CMOV_REG
                }
                VM_BSWAP | VM_SHIFT => {
                    if depth == 0 {
                        return Err(invalid());
                    }
                    op.dst = registers[depth - 1] as u8;
                    if op.code == VM_BSWAP {
                        VM_R_BSWAP
                    } else {
                        VM_R_SHIFT
                    }
                }
                VM_ADD | VM_SUB | VM_BXOR | VM_BAND | VM_BOR | VM_CMP | VM_TEST => {
                    if depth < 2 {
                        return Err(invalid());
                    }
                    op.dst = registers[depth - 2] as u8;
                    op.src = registers[depth - 1] as u8;
                    depth -= if matches!(op.code, VM_CMP | VM_TEST) {
                        2
                    } else {
                        1
                    };
                    match op.code {
                        VM_ADD => VM_R_ADD,
                        VM_SUB => VM_R_SUB,
                        VM_BXOR => VM_R_XOR,
                        VM_BAND => VM_R_AND,
                        VM_BOR => VM_R_OR,
                        VM_CMP => VM_R_CMP,
                        _ => VM_R_TEST,
                    }
                }
                VM_F_MOV_RR..=VM_F_TEST => {
                    if depth != 0 {
                        return Err(invalid());
                    }
                    op.code
                }
                VM_JMP | VM_JCC | VM_NATIVE | VM_RET | VM_TAIL => {
                    if depth != 0 {
                        return Err(invalid());
                    }
                    match op.code {
                        VM_JMP => VM_R_JMP,
                        VM_JCC => VM_R_JCC,
                        VM_NATIVE => VM_R_NATIVE,
                        VM_RET => VM_R_RET,
                        _ => VM_R_TAIL,
                    }
                }
                _ => {
                    return Err(Error::Invariant(
                        "unknown VM operation during register conversion".into(),
                    ));
                }
            };
        }
        if depth != 0 {
            return Err(invalid());
        }
        Ok(())
    }

    pub(super) struct VmImage {
        pub code: Vec<u8>,
        pub entries: BTreeMap<u64, u64>,
        pub moved: BTreeMap<u64, u64>,
        pub lengths: BTreeMap<u64, usize>,
        pub runtime: u64,
        pub islands: Vec<u64>,
        island_frames: Vec<(u64, stack::Site, usize)>,
    }

    #[derive(Debug)]
    pub(super) struct VmFailure {
        pub address: u64,
        pub reason: Error,
    }

    fn gp(register: Register) -> Result<(u8, u8, u8)> {
        let width = u8::try_from(register.size()).map_err(|_| "non-GP operand")?;
        if !matches!(width, 1 | 2 | 4 | 8) {
            return Err("non-GP operand".into());
        }
        let number = register_number(register.full_register())
            .map_err(|_| format!("non-GP register {register:?}"))?;
        let high = u8::from(matches!(
            register,
            Register::AH | Register::BH | Register::CH | Register::DH
        ));
        Ok((number, width, high))
    }

    fn memory_op(instruction: &Instruction, code: u8, width: u8) -> Result<Op> {
        if instruction.segment_prefix() != Register::None {
            return Err("segmented memory operand".into());
        }
        let mut op = Op::new(code, width);
        if instruction.is_ip_rel_memory_operand() {
            op.base = 254;
            op.value = instruction.ip_rel_memory_address() as i64;
            return Ok(op);
        }
        let base = instruction.memory_base();
        op.base = if base == Register::None {
            255
        } else {
            if base.size() != 8 {
                return Err("address-size override".into());
            }
            register_number(base.full_register()).map_err(|_| "non-GP memory base")?
        };
        let index = instruction.memory_index();
        op.index = if index == Register::None {
            255
        } else {
            if index.size() != 8 {
                return Err("address-size override".into());
            }
            register_number(index.full_register()).map_err(|_| "non-GP memory index")?
        };
        if op.base == 255 && op.index == 255 {
            return Err("absolute memory operand".into());
        }
        op.scale = instruction.memory_index_scale() as u8;
        op.value = instruction.memory_displacement64() as i64;
        Ok(op)
    }

    fn operand_width(instruction: &Instruction, operand: u32) -> Result<u8> {
        let size = match instruction.op_kind(operand) {
            OpKind::Register => instruction.op_register(operand).size(),
            OpKind::Memory => instruction.memory_size().size(),
            _ => return Err("unsupported operand width".into()),
        };
        let width = u8::try_from(size).map_err(|_| "unsupported operand width")?;
        if !matches!(width, 1 | 2 | 4 | 8) {
            return Err("unsupported operand width".into());
        }
        Ok(width)
    }

    fn push_operand(instruction: &Instruction, operand: u32, signed: bool) -> Result<Op> {
        let mut op = match instruction.op_kind(operand) {
            OpKind::Register => {
                let (reg, width, high) = gp(instruction.op_register(operand))?;
                let mut op = Op::new(VM_PUSH_REG, width);
                op.reg = reg;
                op.flags = high;
                op
            }
            OpKind::Memory => memory_op(
                instruction,
                VM_PUSH_MEM,
                operand_width(instruction, operand)?,
            )?,
            OpKind::Immediate8
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64 => {
                let mut op = Op::new(VM_PUSH_IMM, 8);
                op.value = instruction
                    .try_immediate(operand)
                    .map_err(|_| "invalid immediate")? as i64;
                op
            }
            _ => return Err("unsupported source operand".into()),
        };
        if signed && op.code != VM_PUSH_IMM {
            op.flags |= 2;
        }
        Ok(op)
    }

    fn pop_operand(instruction: &Instruction, operand: u32) -> Result<Op> {
        match instruction.op_kind(operand) {
            OpKind::Register => {
                let (reg, width, high) = gp(instruction.op_register(operand))?;
                let mut op = Op::new(VM_POP_REG, width);
                op.reg = reg;
                op.flags = high;
                Ok(op)
            }
            OpKind::Memory => memory_op(
                instruction,
                VM_POP_MEM,
                operand_width(instruction, operand)?,
            ),
            _ => Err("unsupported destination operand".into()),
        }
    }

    fn lift(instruction: &Instruction) -> Result<Option<Vec<Op>>> {
        lift_with_stack(instruction, true, true, true, true)
    }

    fn lift_with_stack(
        instruction: &Instruction,
        stack_ops: bool,
        setcc_ops: bool,
        cmov_ops: bool,
        unary_ops: bool,
    ) -> Result<Option<Vec<Op>>> {
        if instruction.has_lock_prefix()
            || instruction.has_rep_prefix()
            || instruction.has_repne_prefix()
        {
            return Ok(None);
        }
        let mnemonic = instruction.mnemonic();
        if matches!(mnemonic, Mnemonic::Nop | Mnemonic::Endbr64) {
            return Ok(Some(Vec::new()));
        }
        if mnemonic == Mnemonic::Ret {
            if instruction.op_count() != 0 {
                return Err("RET with stack adjustment".into());
            }
            return Ok(Some(vec![Op::new(VM_RET, 0)]));
        }
        if setcc_ops
            && matches!(
                mnemonic,
                Mnemonic::Seta
                    | Mnemonic::Setae
                    | Mnemonic::Setb
                    | Mnemonic::Setbe
                    | Mnemonic::Sete
                    | Mnemonic::Setg
                    | Mnemonic::Setge
                    | Mnemonic::Setl
                    | Mnemonic::Setle
                    | Mnemonic::Setne
                    | Mnemonic::Setno
                    | Mnemonic::Setnp
                    | Mnemonic::Setns
                    | Mnemonic::Seto
                    | Mnemonic::Setp
                    | Mnemonic::Sets
            )
            && instruction.op_count() == 1
            && instruction.flow_control() == FlowControl::Next
        {
            let destination = pop_operand(instruction, 0)?;
            if destination.width != 1 {
                return Ok(None);
            }
            let mut condition = Op::new(VM_PUSH_CC, 0);
            condition.flags = condition_opcode(instruction.condition_code())? - 0x80;
            return Ok(Some(vec![condition, destination]));
        }
        if cmov_ops
            && matches!(
                mnemonic,
                Mnemonic::Cmova
                    | Mnemonic::Cmovae
                    | Mnemonic::Cmovb
                    | Mnemonic::Cmovbe
                    | Mnemonic::Cmove
                    | Mnemonic::Cmovg
                    | Mnemonic::Cmovge
                    | Mnemonic::Cmovl
                    | Mnemonic::Cmovle
                    | Mnemonic::Cmovne
                    | Mnemonic::Cmovno
                    | Mnemonic::Cmovnp
                    | Mnemonic::Cmovns
                    | Mnemonic::Cmovo
                    | Mnemonic::Cmovp
                    | Mnemonic::Cmovs
            )
            && instruction.op_count() == 2
            && instruction.flow_control() == FlowControl::Next
            && instruction.op0_kind() == OpKind::Register
            && instruction.op0_register() != Register::RSP
            && matches!(instruction.op1_kind(), OpKind::Register | OpKind::Memory)
        {
            let source = push_operand(instruction, 1, false)?;
            let mut destination = pop_operand(instruction, 0)?;
            if !matches!(source.width, 2 | 4 | 8) || source.width != destination.width {
                return Ok(None);
            }
            destination.code = VM_CMOV_REG;
            destination.flags = condition_opcode(instruction.condition_code())? - 0x80;
            return Ok(Some(vec![source, destination]));
        }
        if matches!(mnemonic, Mnemonic::Inc | Mnemonic::Dec)
            && instruction.flow_control() == FlowControl::Next
            && instruction.op_count() == 1
            && instruction.op0_kind() == OpKind::Register
            && instruction.op0_register() != Register::RSP
        {
            let source = push_operand(instruction, 0, false)?;
            let mut one = Op::new(VM_PUSH_IMM, 8);
            one.value = 1;
            let mut arithmetic = Op::new(
                if mnemonic == Mnemonic::Inc {
                    VM_ADD
                } else {
                    VM_SUB
                },
                source.width,
            );
            arithmetic.flags = VM_PRESERVE_CF;
            return Ok(Some(vec![
                source,
                one,
                arithmetic,
                pop_operand(instruction, 0)?,
            ]));
        }
        if unary_ops
            && matches!(mnemonic, Mnemonic::Neg | Mnemonic::Not)
            && instruction.flow_control() == FlowControl::Next
            && instruction.op_count() == 1
            && !(instruction.op0_kind() == OpKind::Register
                && instruction.op0_register() == Register::RSP)
        {
            let source = push_operand(instruction, 0, false)?;
            let mut immediate = Op::new(VM_PUSH_IMM, 8);
            let mut arithmetic = Op::new(
                if mnemonic == Mnemonic::Neg {
                    VM_SUB
                } else {
                    VM_BXOR
                },
                source.width,
            );
            let destination = pop_operand(instruction, 0)?;
            if mnemonic == Mnemonic::Neg {
                return Ok(Some(vec![immediate, source, arithmetic, destination]));
            }
            immediate.value = -1;
            arithmetic.flags = VM_PRESERVE_FLAGS;
            return Ok(Some(vec![source, immediate, arithmetic, destination]));
        }
        if unary_ops
            && mnemonic == Mnemonic::Bswap
            && instruction.flow_control() == FlowControl::Next
            && instruction.op_count() == 1
            && instruction.op0_kind() == OpKind::Register
            && instruction.op0_register() != Register::RSP
        {
            let source = push_operand(instruction, 0, false)?;
            if !matches!(source.width, 4 | 8) {
                return Ok(None);
            }
            return Ok(Some(vec![
                source,
                Op::new(VM_BSWAP, source.width),
                pop_operand(instruction, 0)?,
            ]));
        }
        if unary_ops
            && matches!(
                mnemonic,
                Mnemonic::Shl
                    | Mnemonic::Sal
                    | Mnemonic::Shr
                    | Mnemonic::Sar
                    | Mnemonic::Rol
                    | Mnemonic::Ror
            )
            && instruction.flow_control() == FlowControl::Next
            && instruction.op_count() == 2
            && instruction.op0_kind() == OpKind::Register
            && instruction.op0_register().full_register() != Register::RSP
            && instruction.op1_kind() == OpKind::Immediate8
        {
            let source = push_operand(instruction, 0, false)?;
            let count = instruction.immediate8() & if source.width == 8 { 63 } else { 31 };
            if count == 0 || count >= source.width * 8 {
                return Ok(None);
            }
            let mut shift = Op::new(VM_SHIFT, source.width);
            shift.flags = match mnemonic {
                Mnemonic::Shl | Mnemonic::Sal => VM_SHIFT_LEFT,
                Mnemonic::Shr => VM_SHIFT_RIGHT,
                Mnemonic::Sar => VM_SHIFT_ARITH,
                Mnemonic::Rol => VM_ROTATE_LEFT,
                Mnemonic::Ror => VM_ROTATE_RIGHT,
                _ => unreachable!(),
            };
            shift.value = i64::from(count);
            return Ok(Some(vec![source, shift, pop_operand(instruction, 0)?]));
        }
        if stack_ops
            && instruction.flow_control() == FlowControl::Next
            && instruction.op_count() == 1
        {
            let rsp = register_number(Register::RSP)?;
            if mnemonic == Mnemonic::Push {
                let source = match instruction.op0_kind() {
                    OpKind::Register
                        if instruction.op0_register().size() == 8
                            && instruction.op0_register() != Register::RSP =>
                    {
                        push_operand(instruction, 0, false)?
                    }
                    OpKind::Immediate8to64 | OpKind::Immediate32to64 => {
                        push_operand(instruction, 0, false)?
                    }
                    OpKind::Memory if instruction.memory_size().size() == 8 => {
                        push_operand(instruction, 0, false)?
                    }
                    _ => return Ok(None),
                };
                let mut address = Op::new(VM_LEA, 8);
                address.base = rsp;
                address.value = -8;
                let mut set_rsp = Op::new(VM_POP_REG, 8);
                set_rsp.reg = rsp;
                let mut store = Op::new(VM_POP_MEM, 8);
                store.base = rsp;
                return Ok(Some(vec![source, address, set_rsp, store]));
            }
            if mnemonic == Mnemonic::Pop
                && match instruction.op0_kind() {
                    OpKind::Register => {
                        instruction.op0_register().size() == 8
                            && instruction.op0_register() != Register::RSP
                    }
                    OpKind::Memory => instruction.memory_size().size() == 8,
                    _ => false,
                }
            {
                let mut load = Op::new(VM_PUSH_MEM, 8);
                load.base = rsp;
                let mut address = Op::new(VM_LEA, 8);
                address.base = rsp;
                address.value = 8;
                let mut set_rsp = Op::new(VM_POP_REG, 8);
                set_rsp.reg = rsp;
                return Ok(Some(vec![
                    load,
                    address,
                    set_rsp,
                    pop_operand(instruction, 0)?,
                ]));
            }
        }
        if instruction.flow_control() != FlowControl::Next || instruction.op_count() != 2 {
            return Ok(None);
        }
        let code = match mnemonic {
            Mnemonic::Xchg => {
                if instruction.op0_kind() != OpKind::Register
                    || instruction.op1_kind() != OpKind::Register
                    || instruction.op0_register().full_register() == Register::RSP
                    || instruction.op1_register().full_register() == Register::RSP
                {
                    return Ok(None);
                }
                let left = push_operand(instruction, 0, false)?;
                let right = push_operand(instruction, 1, false)?;
                if left.width != right.width {
                    return Ok(None);
                }
                if instruction.op0_register() == instruction.op1_register() && left.width != 4 {
                    return Ok(Some(Vec::new()));
                }
                return Ok(Some(vec![
                    left,
                    right,
                    pop_operand(instruction, 0)?,
                    pop_operand(instruction, 1)?,
                ]));
            }
            Mnemonic::Mov => {
                let src = push_operand(instruction, 1, false)?;
                let dst = pop_operand(instruction, 0)?;
                if src.code != VM_PUSH_IMM && src.width != dst.width {
                    return Ok(None);
                }
                return Ok(Some(vec![src, dst]));
            }
            Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd => {
                let src = push_operand(instruction, 1, mnemonic != Mnemonic::Movzx)?;
                let dst = pop_operand(instruction, 0)?;
                if src.width >= dst.width {
                    return Ok(None);
                }
                return Ok(Some(vec![src, dst]));
            }
            Mnemonic::Lea => {
                if instruction.op1_kind() != OpKind::Memory {
                    return Ok(None);
                }
                let mut addr = memory_op(instruction, VM_LEA, 8)?;
                let dst = pop_operand(instruction, 0)?;
                addr.width = dst.width;
                return Ok(Some(vec![addr, dst]));
            }
            Mnemonic::Add => VM_ADD,
            Mnemonic::Sub => VM_SUB,
            Mnemonic::Adc => VM_ADD,
            Mnemonic::Sbb => VM_SUB,
            Mnemonic::Xor => VM_BXOR,
            Mnemonic::And => VM_BAND,
            Mnemonic::Or => VM_BOR,
            Mnemonic::Cmp => VM_CMP,
            Mnemonic::Test => VM_TEST,
            _ => return Ok(None),
        };
        let width = operand_width(instruction, 0)?;
        let left = push_operand(instruction, 0, false)?;
        let right = push_operand(instruction, 1, false)?;
        if right.code != VM_PUSH_IMM && right.width != width {
            return Ok(None);
        }
        let mut arithmetic = Op::new(code, width);
        if matches!(mnemonic, Mnemonic::Adc | Mnemonic::Sbb) {
            arithmetic.flags = VM_USE_CF;
        }
        let mut result = vec![left, right, arithmetic];
        if code != VM_CMP && code != VM_TEST {
            result.push(pop_operand(instruction, 0)?);
        }
        Ok(Some(result))
    }

    fn fuse(ops: &[Op]) -> Vec<Op> {
        if ops.len() == 2 && ops[1].code == VM_POP_REG {
            let source = &ops[0];
            let destination = &ops[1];
            if (source.width == destination.width || source.code == VM_PUSH_IMM)
                && source.flags & 2 == 0
            {
                let code = match source.code {
                    VM_PUSH_REG => VM_F_MOV_RR,
                    VM_PUSH_IMM => VM_F_MOV_IR,
                    VM_PUSH_MEM => VM_F_LOAD,
                    _ => return ops.to_vec(),
                };
                let mut fused = Op::new(code, destination.width);
                fused.dst = destination.reg;
                fused.src = if source.code == VM_PUSH_REG {
                    source.reg
                } else {
                    255
                };
                fused.base = source.base;
                fused.index = source.index;
                fused.scale = source.scale;
                fused.value = source.value;
                fused.flags = (destination.flags & 1) | ((source.flags & 1) << 1);
                return vec![fused];
            }
        }
        if ops.len() == 2
            && ops[0].code == VM_PUSH_REG
            && ops[1].code == VM_POP_MEM
            && ops[0].width == ops[1].width
            && ops[0].flags & 2 == 0
        {
            let mut fused = Op::new(VM_F_STORE, ops[1].width);
            fused.src = ops[0].reg;
            fused.base = ops[1].base;
            fused.index = ops[1].index;
            fused.scale = ops[1].scale;
            fused.value = ops[1].value;
            fused.flags = (ops[0].flags & 1) << 1;
            return vec![fused];
        }
        if ops.len() >= 3
            && ops[0].code == VM_PUSH_REG
            && matches!(ops[1].code, VM_PUSH_REG | VM_PUSH_IMM)
            && matches!(
                ops[2].code,
                VM_ADD | VM_SUB | VM_BXOR | VM_BAND | VM_BOR | VM_CMP | VM_TEST
            )
            && (ops[1].code == VM_PUSH_IMM || ops[0].width == ops[1].width)
            && ops[0].flags & 2 == 0
            && ops[1].flags & 2 == 0
            && ops[2].flags == 0
            && (ops.len() == 3 && matches!(ops[2].code, VM_CMP | VM_TEST)
                || ops.len() == 4
                    && ops[3].code == VM_POP_REG
                    && ops[3].reg == ops[0].reg
                    && ops[3].width == ops[0].width
                    && ops[3].flags == ops[0].flags)
        {
            let code = match ops[2].code {
                VM_ADD => VM_F_ADD,
                VM_SUB => VM_F_SUB,
                VM_BXOR => VM_F_XOR,
                VM_BAND => VM_F_AND,
                VM_BOR => VM_F_OR,
                VM_CMP => VM_F_CMP,
                _ => VM_F_TEST,
            };
            let mut fused = Op::new(code, ops[2].width);
            fused.dst = ops[0].reg;
            fused.src = if ops[1].code == VM_PUSH_REG {
                ops[1].reg
            } else {
                255
            };
            fused.value = if ops[1].code == VM_PUSH_IMM {
                ops[1].value
            } else {
                0
            };
            fused.flags = (ops[0].flags & 1) | ((ops[1].flags & 1) << 1);
            return vec![fused];
        }
        ops.to_vec()
    }

    fn escape_ok(instruction: &Instruction) -> Result<()> {
        if !matches!(
            instruction.flow_control(),
            FlowControl::Next | FlowControl::Call | FlowControl::IndirectCall
        ) {
            return Err("unsupported native control transfer".into());
        }
        if instruction.is_privileged()
            || matches!(
                instruction.mnemonic(),
                Mnemonic::Syscall
                    | Mnemonic::Sysenter
                    | Mnemonic::Int
                    | Mnemonic::Int1
                    | Mnemonic::Int3
                    | Mnemonic::Hlt
                    | Mnemonic::Ud2
            )
            || whole_simd_state(instruction.mnemonic())
        {
            return Err(format!("unsafe native escape at 0x{:x}", instruction.ip()).into());
        }
        Ok(())
    }

    fn executable_target(binary: &elf::Binary, target: u64) -> bool {
        binary.segments().any(|seg| {
            seg.p_type() == elf::segment::Type::LOAD
                && seg.flags() & elf::segment::Flags::X.bits() != 0
                && in_range(
                    target,
                    seg.virtual_address(),
                    seg.virtual_address().saturating_add(seg.physical_size()),
                )
        })
    }

    fn plt_slot(bytes: &[u8], address: u64) -> Option<u64> {
        let mut prefix = usize::from(bytes.starts_with(&ENDBR64)) * ENDBR64.len();
        if bytes.get(prefix) == Some(&0xf2) {
            prefix += 1;
        }
        if bytes.get(prefix..prefix + 2) != Some(&[0xff, 0x25]) {
            return None;
        }
        let displacement = i32::from_le_bytes(bytes.get(prefix + 2..prefix + 6)?.try_into().ok()?);
        address
            .checked_add((prefix + 6) as u64)?
            .checked_add_signed(displacement as i64)
    }

    fn noreturn_plt_call(binary: &elf::Binary, instruction: &Instruction) -> bool {
        if instruction.flow_control() != FlowControl::Call || !instruction.is_call_near() {
            return false;
        }
        let target = instruction.near_branch_target();
        if !executable_target(binary, target)
            || !binary.sections().any(|section| {
                matches!(section.name().as_str(), ".plt" | ".plt.sec")
                    && section
                        .virtual_address()
                        .checked_add(section.size())
                        .is_some_and(|end| in_range(target, section.virtual_address(), end))
            })
        {
            return false;
        }
        let Some(slot) = plt_slot(binary.content_from_virtual_address(target, 11), target) else {
            return false;
        };
        let mut matches = binary.relocations().filter(|rel| rel.address() == slot);
        let Some(rel) = matches.next() else {
            return false;
        };
        matches.next().is_none()
            && rel.get_type() == relocation::Type::X86_64_JUMP_SLOT
            && rel.purpose() == relocation::Purpose::PLTGOT
            && rel.is_rela()
            && rel.addend() == 0
            && rel.symbol().is_some_and(|symbol| {
                matches!(symbol.name().as_str(), "__stack_chk_fail" | "__assert_fail")
            })
    }

    fn terminal_noreturn(function: &Function, binary: &elf::Binary) -> BTreeSet<u64> {
        function
            .blocks
            .iter()
            .filter(|block| matches!(block.exit, Exit::Fallthrough(end) if end == function.end))
            .filter(|block| {
                block.body.last().is_some_and(|instruction| {
                    instruction.next_ip() == function.end && noreturn_plt_call(binary, instruction)
                })
            })
            .map(|block| block.old)
            .collect()
    }

    pub(super) fn plan(function: &Function, binary: &elf::Binary) -> Result<VmPlan> {
        plan_with_stack(function, binary, true, true, true, true)
    }

    fn plan_with_stack(
        function: &Function,
        binary: &elf::Binary,
        stack_ops: bool,
        setcc_ops: bool,
        cmov_ops: bool,
        unary_ops: bool,
    ) -> Result<VmPlan> {
        if !function.tables.is_empty() || !function.dispatches.is_empty() {
            return Err("computed jump requires native route mode".into());
        }
        if let Some(rows) = &function.unwind {
            for label in std::iter::once(function.start)
                .chain(function.entries.iter().map(|entry| entry.label))
            {
                let rule = super::unwind_rule(rows, label)?;
                if rule.cfa_register != 7
                    || rule.cfa_offset != 8
                    || rule.cfa_expression.is_some()
                    || rule.registers.get(&16) != Some(&FrameRegisterRule::Offset(-8))
                {
                    return Err("noncanonical entry unwind rule".into());
                }
            }
        } else if function.entries.len() > 1 {
            return Err("multiple entries lack unwind proof".into());
        }
        let noreturn = terminal_noreturn(function, binary);
        let stack = stack::plan(function, &noreturn)?;
        let mut blocks = Vec::new();
        let mut islands = Vec::new();
        let mut lifted = 0;
        for block in &function.blocks {
            if !stack.reachable.contains(&block.old) {
                continue;
            }
            let mut ops = Vec::new();
            for instruction in &block.body {
                let site = stack
                    .sites
                    .get(&instruction.ip())
                    .ok_or_else(|| Error::Invariant("VM stack site missing".into()))?;
                let mut adjusted = *instruction;
                if site.displacement != 0 {
                    adjusted.set_memory_displacement64(
                        adjusted
                            .memory_displacement64()
                            .wrapping_add_signed(site.displacement),
                    );
                }
                let lowered = if stack_ops && setcc_ops && cmov_ops && unary_ops {
                    lift(&adjusted)
                } else {
                    lift_with_stack(&adjusted, stack_ops, setcc_ops, cmov_ops, unary_ops)
                };
                match lowered.map_err(Error::eligibility) {
                    Ok(Some(code)) => {
                        let code = fuse(&code);
                        if !code.is_empty() && instruction.mnemonic() != Mnemonic::Ret {
                            lifted += 1;
                        }
                        ops.extend(code);
                    }
                    Ok(None) | Err(Error::Unsupported(_)) => {
                        escape_ok(instruction)?;
                        let mut op = Op::new(VM_NATIVE, 0);
                        op.target = Target::Island(islands.len());
                        ops.push(op);
                        islands.push(NativeIsland {
                            instruction: adjusted,
                            stack: *site,
                        });
                    }
                    Err(error) => return Err(error),
                }
            }
            match block.exit {
                Exit::Branch {
                    target,
                    fallthrough,
                    cc,
                } => {
                    if !in_range(target, function.start, function.end)
                        || !in_range(fallthrough, function.start, function.end)
                    {
                        return Err("branch leaves function".into());
                    }
                    let mut branch = Op::new(VM_JCC, 0);
                    branch.flags = condition_opcode(cc)? - 0x80;
                    branch.target = Target::Block(target);
                    ops.push(branch);
                    let mut jump = Op::new(VM_JMP, 0);
                    jump.target = Target::Block(fallthrough);
                    ops.push(jump);
                }
                Exit::Jump(target) if !in_range(target, function.start, function.end) => {
                    if !executable_target(binary, target) {
                        return Err("VM tail target is not executable".into());
                    }
                    let mut tail = Op::new(VM_TAIL, 0);
                    tail.target = Target::External(target);
                    ops.push(tail);
                }
                Exit::Fallthrough(target)
                    if target == function.end && noreturn.contains(&block.old) =>
                {
                    let mut abort = Op::new(VM_TAIL, 0);
                    abort.target = Target::Abort;
                    ops.push(abort);
                }
                Exit::Jump(target) | Exit::Fallthrough(target) => {
                    if !in_range(target, function.start, function.end) {
                        return Err("control flow leaves function".into());
                    }
                    let mut jump = Op::new(VM_JMP, 0);
                    jump.target = Target::Block(target);
                    ops.push(jump);
                }
                Exit::Return => {
                    if ops.last().is_none_or(|op| op.code != VM_RET) {
                        return Err("unsupported return".into());
                    }
                }
                Exit::Table(_) | Exit::Dispatch(_) => unreachable!(),
            }
            blocks.push(VmBlock {
                old: block.old,
                ops,
            });
        }
        if lifted == 0 {
            return Err("no instructions lift into bytecode".into());
        }
        let op_count = blocks.iter().map(|block| block.ops.len()).sum();
        if op_count > 65535 {
            if unary_ops {
                return plan_with_stack(function, binary, stack_ops, setcc_ops, cmov_ops, false);
            }
            if stack_ops {
                return plan_with_stack(function, binary, false, setcc_ops, cmov_ops, false);
            }
            if setcc_ops {
                return plan_with_stack(function, binary, false, false, cmov_ops, false);
            }
            if cmov_ops {
                return plan_with_stack(function, binary, false, false, false, false);
            }
            return Err("VM bytecode exceeds operation limit".into());
        }
        if blocks.is_empty() || blocks.len() > u16::MAX as usize {
            return Err("VM block count exceeds limit".into());
        }
        if blocks.iter().any(|block| block.ops.is_empty()) {
            return Err("VM block has no operations".into());
        }
        Ok(VmPlan {
            architecture: Architecture::Stack,
            blocks,
            relays: Vec::new(),
            islands,
            op_count,
            max_depth: frame_depth(stack.max_depth)?,
        })
    }

    pub(super) fn capacity(selected: &[Selected]) -> Result<usize> {
        let mut len = align_up(RUNTIME.len(), 16)?;
        for item in selected.iter().filter(|item| item.mode() == Mode::Vm) {
            let plan = item
                .vm()
                .ok_or_else(|| Error::Invariant("VM plan missing".into()))?;
            len = align_up(len, 8)?
                .checked_add(VM_CODEC_LEN)
                .and_then(|value| value.checked_add(plan.op_count * OP_LEN))
                .and_then(|value| value.checked_add((plan.blocks.len() + plan.relays.len()) * 4))
                .and_then(|value| value.checked_add(plan.blocks.len() * (THUNK_LEN + META_LEN)))
                .and_then(|value| value.checked_add(plan.islands.len() * ISLAND_LEN))
                .ok_or("VM region too large")?;
        }
        align_up(len, 16)
    }

    fn put_vm(code: &mut [u8], base: u64, va: u64, bytes: &[u8]) -> Result<()> {
        let offset = va
            .checked_sub(base)
            .ok_or_else(|| Error::Invariant("VM address underflow".into()))?;
        let range =
            super::file_range(code.len(), offset, bytes.len() as u64).map_err(Error::invariant)?;
        let slot = &mut code[range];
        slot.copy_from_slice(bytes);
        Ok(())
    }

    pub(super) fn encode(
        selected: &[Selected],
        placed_entries: &BTreeMap<u64, u64>,
        base: u64,
        seed: u64,
    ) -> std::result::Result<VmImage, VmFailure> {
        let first = selected
            .iter()
            .find(|item| item.mode() == Mode::Vm)
            .map(|item| item.function.start)
            .unwrap_or(0);
        let failure = |reason: Error| VmFailure {
            address: first,
            reason: reason.eligibility(),
        };
        let mut code = vec![0xcc; capacity(selected).map_err(&failure)?];
        code[..RUNTIME.len()].copy_from_slice(RUNTIME);
        let mut cursor = align_up(RUNTIME.len(), 16).map_err(&failure)?;
        struct TailFixup {
            owner: u64,
            architecture: Architecture,
            at: u64,
            pc: usize,
            op: Op,
        }
        let mut tail_fixups = Vec::new();
        let mut moved = BTreeMap::new();
        let mut lengths = BTreeMap::new();
        let mut entries = BTreeMap::new();
        let mut island_addresses = Vec::new();
        let mut island_frames = Vec::new();
        for item in selected.iter().filter(|item| item.mode() == Mode::Vm) {
            let function_result = (|| -> Result<()> {
                let plan = item
                    .vm()
                    .ok_or_else(|| Error::Invariant("VM plan missing".into()))?;
                let order = permute_all(
                    plan.blocks.len(),
                    function_seed(seed ^ 0xb7e151628aed2a6b, item.function.start),
                );
                let relay_order = permute_all(
                    plan.relays.len(),
                    function_seed(seed ^ RELAY_SITE_SALT, item.function.start),
                );
                cursor = align_up(cursor, 8)?;
                let codec_va = base + cursor as u64;
                let codec = Codec::new(seed, item.function.start, plan.architecture);
                put_vm(
                    &mut code,
                    base,
                    codec_va,
                    &codec.descriptor(plan.blocks.len() + plan.relays.len(), plan.op_count)?,
                )?;
                cursor += VM_CODEC_LEN;
                let ops_va = base + cursor as u64;
                cursor += plan.op_count * OP_LEN;
                let table_va = base + cursor as u64;
                cursor += (plan.blocks.len() + plan.relays.len()) * 4;
                let mut pc = BTreeMap::new();
                let mut count = 0usize;
                for &index in &order {
                    pc.insert(plan.blocks[index].old, count);
                    count += plan.blocks[index].ops.len();
                }
                let mut relay_pc = vec![0; plan.relays.len()];
                for &index in &relay_order {
                    relay_pc[index] = count;
                    count += plan.relays[index].len();
                }
                if count != plan.op_count {
                    return Err(Error::Invariant("VM operation count changed".into()));
                }
                let dispatch = dispatch(plan, &pc, &relay_pc, &codec)?;
                put_vm(&mut code, base, table_va, &dispatch.bytes)?;
                let mut thunks = BTreeMap::new();
                for &index in &order {
                    let old = plan.blocks[index].old;
                    let thunk = base + cursor as u64;
                    let meta = thunk + THUNK_LEN as u64;
                    thunks.insert(old, thunk);
                    let mut bytes = ENDBR64.to_vec();
                    bytes.extend_from_slice(&[0x41, 0x53, 0x4c, 0x8d, 0x1d]);
                    bytes.extend_from_slice(&rel32(thunk + 13, meta)?);
                    bytes.push(0xe9);
                    bytes.extend_from_slice(&rel32(
                        thunk + THUNK_LEN as u64,
                        base + VM_ENTER_OFF as u64,
                    )?);
                    if bytes.len() != THUNK_LEN {
                        return Err(Error::Invariant("VM thunk length mismatch".into()));
                    }
                    put_vm(&mut code, base, thunk, &bytes)?;
                    let metadata = encode_metadata(
                        ops_va as i64 - meta as i64,
                        pc[&old] as u32,
                        plan.op_count as u32,
                        codec_va as i64 - meta as i64,
                        plan.max_depth,
                    );
                    put_vm(&mut code, base, meta, &metadata)?;
                    cursor += THUNK_LEN + META_LEN;
                    moved.insert(old, thunk);
                    lengths.insert(old, THUNK_LEN);
                }
                for entry in &item.function.entries {
                    if placed_entries.contains_key(&entry.label)
                        || entries.insert(entry.label, thunks[&entry.label]).is_some()
                    {
                        return Err(Error::Invariant("duplicate VM entry address".into()));
                    }
                }
                let mut islands = Vec::new();
                for _ in &plan.islands {
                    islands.push(base + cursor as u64);
                    cursor += ISLAND_LEN;
                }
                let mut op_index = 0;
                let mut continuations = vec![None; plan.islands.len()];
                for ops in order
                    .iter()
                    .map(|&index| plan.blocks[index].ops.as_slice())
                    .chain(
                        relay_order
                            .iter()
                            .map(|&index| plan.relays[index].as_slice()),
                    )
                {
                    for op in ops {
                        let at = ops_va + (op_index * OP_LEN) as u64;
                        let value = if op.base == 254 {
                            op.value - at as i64
                        } else {
                            op.value
                        };
                        let target = match op.target {
                            Target::None => 0,
                            Target::Block(_) | Target::Relay(_) => {
                                *dispatch.tokens.get(&op.target).ok_or_else(|| {
                                    Error::Invariant("VM branch token missing".into())
                                })? as i64
                            }
                            Target::Island(index) => {
                                continuations[index] = Some((op_index + 1) as u32);
                                islands[index] as i64 - at as i64
                            }
                            Target::External(_) => {
                                tail_fixups.push(TailFixup {
                                    owner: item.function.start,
                                    architecture: plan.architecture,
                                    at,
                                    pc: op_index,
                                    op: *op,
                                });
                                0
                            }
                            Target::Abort => base as i64 + VM_ABORT_OFF as i64 - at as i64,
                        };
                        let bytes = codec.encode_record(
                            serialize_op(op, plan.architecture, value, target),
                            op_index,
                        )?;
                        put_vm(&mut code, base, at, &bytes)?;
                        op_index += 1;
                    }
                }
                for (index, island) in plan.islands.iter().enumerate() {
                    let va = islands[index];
                    let instruction = &island.instruction;
                    let mut escaped = *instruction;
                    if escaped.flow_control() == FlowControl::Call && escaped.is_call_near() {
                        let target = escaped.near_branch_target();
                        if in_range(target, item.function.start, item.function.end) {
                            escaped.set_near_branch64(*thunks.get(&target).ok_or_else(|| {
                                Error::Invariant("VM call target missing".into())
                            })?);
                        }
                    }
                    let encoded = BlockEncoder::encode(
                        64,
                        InstructionBlock::new(std::slice::from_ref(&escaped), va + 8),
                        BlockEncoderOptions::NONE,
                    )
                    .map_err(|e| {
                        format!("cannot relocate VM escape at 0x{:x}: {e}", instruction.ip())
                    })?;
                    if encoded.code_buffer.len() > ISLAND_LEN - 43 {
                        return Err(
                            format!("VM escape too large at 0x{:x}", instruction.ip()).into()
                        );
                    }
                    let mut decoder =
                        Decoder::with_ip(64, &encoded.code_buffer, va + 8, DecoderOptions::NONE);
                    let relocated = decoder.decode();
                    if relocated.is_invalid() || decoder.can_decode() {
                        return Err(format!(
                            "VM escape has inline data at 0x{:x}",
                            instruction.ip()
                        )
                        .into());
                    }
                    let mut bytes = ENDBR64.to_vec();
                    bytes.extend_from_slice(&[0x48, 0x8b, 0x24, 0x24]);
                    bytes.extend_from_slice(&encoded.code_buffer);
                    bytes.extend_from_slice(&[0x48, 0x8d, 0xa4, 0x24, 0x80, 0xff, 0xff, 0xff]);
                    bytes.extend_from_slice(&[0x9c, 0x41, 0x57]);
                    bytes.extend_from_slice(&[0x4c, 0x8d, 0xbc, 0x24]);
                    let displacement = i32::try_from(160 - island.stack.after)
                        .map_err(|_| "VM context recovery offset exceeds 32 bits")?;
                    bytes.extend_from_slice(&displacement.to_le_bytes());
                    bytes.extend_from_slice(&[0x49, 0xc7, 0x87]);
                    bytes.extend_from_slice(&(VM_PC as u32).to_le_bytes());
                    bytes.extend_from_slice(
                        &continuations[index]
                            .ok_or_else(|| Error::Invariant("VM continuation missing".into()))?
                            .to_le_bytes(),
                    );
                    bytes.push(0xe9);
                    bytes.extend_from_slice(&rel32(
                        va + bytes.len() as u64 + 4,
                        base + VM_NATIVE_LEAVE_OFF as u64,
                    )?);
                    put_vm(&mut code, base, va, &bytes)?;
                    island_addresses.push(va);
                    island_frames.push((va, island.stack, encoded.code_buffer.len()));
                }
                Ok(())
            })();
            function_result.map_err(|reason| VmFailure {
                address: item.function.start,
                reason: reason.eligibility(),
            })?;
        }
        for fixup in tail_fixups {
            let patched = (|| -> Result<()> {
                let Target::External(old) = fixup.op.target else {
                    return Err(Error::Invariant("VM tail fixup has no target".into()));
                };
                let new = entries
                    .get(&old)
                    .or_else(|| placed_entries.get(&old))
                    .copied()
                    .unwrap_or(old);
                if new == old
                    && selected
                        .iter()
                        .any(|item| in_range(old, item.function.start, item.function.end))
                {
                    return Err("VM tail target lacks a rewritten entry".into());
                }
                let codec = Codec::new(seed, fixup.owner, fixup.architecture);
                let bytes = codec.encode_record(
                    serialize_op(
                        &fixup.op,
                        fixup.architecture,
                        fixup.op.value,
                        new as i64 - fixup.at as i64,
                    ),
                    fixup.pc,
                )?;
                put_vm(&mut code, base, fixup.at, &bytes)
            })();
            patched.map_err(|reason| VmFailure {
                address: fixup.owner,
                reason: reason.eligibility(),
            })?;
        }
        Ok(VmImage {
            code,
            entries,
            moved,
            lengths,
            runtime: base,
            islands: island_addresses,
            island_frames,
        })
    }

    pub(super) fn runtime_len() -> usize {
        RUNTIME.len()
    }

    pub(super) fn runtime_offsets() -> [usize; 6] {
        [
            VM_ENTER_OFF,
            VM_NATIVE_ENTER_OFF,
            VM_NATIVE_LEAVE_OFF,
            VM_FINISH_OFF,
            VM_ABORT_OFF,
            VM_RUN_OFF,
        ]
    }

    fn entry_rule(offset: i32) -> UnwindRule {
        UnwindRule {
            cfa_register: 7,
            cfa_offset: offset,
            cfa_expression: None,
            registers: BTreeMap::from([(16, FrameRegisterRule::Offset(-8))]),
        }
    }

    fn context_rule() -> UnwindRule {
        let mut cfa = vec![0x7f];
        sleb(VM_ENTRY_RSP as i64, &mut cfa);
        cfa.push(0x06);
        cfa.push(0x23);
        uleb(8, &mut cfa);
        let mut registers = BTreeMap::from([(16, FrameRegisterRule::Offset(-8))]);
        for (register, offset) in [
            (3, VM_ENTRY_SAVED),
            (6, VM_ENTRY_SAVED + 8),
            (12, VM_ENTRY_SAVED + 16),
            (13, VM_ENTRY_SAVED + 24),
            (14, VM_ENTRY_SAVED + 32),
            (15, VM_ENTRY_SAVED + 40),
        ] {
            let mut expression = vec![0x7f];
            sleb(offset as i64, &mut expression);
            registers.insert(register, FrameRegisterRule::Expression(expression));
        }
        UnwindRule {
            cfa_register: 15,
            cfa_offset: 0,
            cfa_expression: Some(cfa),
            registers,
        }
    }

    fn stack_context_rule(context_slot: i64, entry_slot: i64) -> UnwindRule {
        let mut cfa = vec![0x77];
        sleb(
            if context_slot == 16 {
                context_slot
            } else {
                entry_slot
            },
            &mut cfa,
        );
        cfa.push(0x06);
        if context_slot == 16 {
            cfa.push(0x23);
            uleb(VM_ENTRY_RSP as u64, &mut cfa);
            cfa.push(0x06);
        }
        cfa.push(0x23);
        uleb(8, &mut cfa);
        let mut registers = BTreeMap::from([(16, FrameRegisterRule::Offset(-8))]);
        for (register, offset) in [
            (3, VM_ENTRY_SAVED),
            (6, VM_ENTRY_SAVED + 8),
            (12, VM_ENTRY_SAVED + 16),
            (13, VM_ENTRY_SAVED + 24),
            (14, VM_ENTRY_SAVED + 32),
            (15, VM_ENTRY_SAVED + 40),
        ] {
            let mut expression = vec![0x77];
            sleb(context_slot, &mut expression);
            expression.push(0x06);
            expression.push(0x23);
            uleb(offset as u64, &mut expression);
            registers.insert(register, FrameRegisterRule::Expression(expression));
        }
        UnwindRule {
            cfa_register: 7,
            cfa_offset: 0,
            cfa_expression: Some(cfa),
            registers,
        }
    }

    fn guest_rule(depth: i64) -> Result<UnwindRule> {
        let offset = i32::try_from(VM_FRAME_SHIFT as i64 + 8 - depth)
            .map_err(|_| "VM unwind offset exceeds 32 bits")?;
        let mut rule = entry_rule(offset);
        for (register, slot) in [(3, 0), (6, 8), (12, 16), (13, 24), (14, 32), (15, 40)] {
            rule.registers.insert(
                register,
                FrameRegisterRule::Offset(
                    i32::try_from(
                        VM_CONTEXT_OFFSET as i64 + VM_ENTRY_SAVED as i64 + slot
                            - VM_FRAME_SHIFT as i64
                            - 8,
                    )
                    .map_err(|_| "VM saved register offset exceeds 32 bits")?,
                ),
            );
        }
        Ok(rule)
    }

    pub(super) fn frame_regions(
        image: &VmImage,
        selected: &[Selected],
    ) -> Result<Vec<FrameRegion>> {
        let mut regions = Vec::new();
        let mut rows = vec![(0, entry_rule(16))];
        let mut decoder = Decoder::with_ip(
            64,
            &RUNTIME[VM_ENTER_OFF..VM_CONTEXT_READY_OFF],
            VM_ENTER_OFF as u64,
            DecoderOptions::NONE,
        );
        let mut offset = 16;
        let mut saved = BTreeMap::new();
        while decoder.can_decode() {
            let instruction = decoder.decode();
            if instruction.is_invalid() {
                return Err(Error::Invariant("invalid VM entry code".into()));
            }
            if matches!(instruction.mnemonic(), Mnemonic::Push | Mnemonic::Pushfq) {
                offset += 8;
                let dwarf = match instruction.op0_register() {
                    Register::RBX => Some(3),
                    Register::RBP => Some(6),
                    Register::R12 => Some(12),
                    Register::R13 => Some(13),
                    Register::R14 => Some(14),
                    Register::R15 => Some(15),
                    _ => None,
                };
                if let Some(register) = dwarf {
                    saved.insert(register, FrameRegisterRule::Offset(-offset));
                }
                if instruction.next_ip() < VM_CONTEXT_READY_OFF as u64 {
                    let mut rule = entry_rule(offset);
                    rule.registers.extend(saved.clone());
                    rows.push((instruction.next_ip() as u32, rule));
                }
            }
        }
        regions.push(FrameRegion {
            va: image.runtime + VM_ENTER_OFF as u64,
            len: (VM_CONTEXT_READY_OFF - VM_ENTER_OFF) as u32,
            rows,
        });
        for (start, end, rule) in [
            (VM_CONTEXT_READY_OFF, VM_NATIVE_RESTORED_OFF, context_rule()),
            (
                VM_NATIVE_RESTORED_OFF,
                VM_NATIVE_LEAVE_OFF,
                stack_context_rule(16, 0),
            ),
            (VM_NATIVE_LEAVE_OFF, VM_FINISH_RESTORED_OFF, context_rule()),
            (
                VM_FINISH_RESTORED_OFF,
                VM_RETURN_OFF,
                stack_context_rule(0, 8),
            ),
            (VM_RETURN_OFF, VM_TAIL_OFF, entry_rule(8)),
            (VM_TAIL_OFF, VM_TAIL_RESTORED_OFF, context_rule()),
            (
                VM_TAIL_RESTORED_OFF,
                VM_TAIL_JUMP_OFF,
                stack_context_rule(0, 8),
            ),
            (VM_TAIL_JUMP_OFF, VM_ABORT_OFF, entry_rule(8)),
            (VM_ABORT_OFF, VM_RUN_OFF, context_rule()),
        ] {
            regions.push(FrameRegion {
                va: image.runtime + start as u64,
                len: (end - start) as u32,
                rows: vec![(0, rule)],
            });
        }
        regions.push(FrameRegion {
            va: image.runtime + VM_RUN_OFF as u64,
            len: (RUNTIME.len() - VM_RUN_OFF) as u32,
            rows: vec![(0, context_rule())],
        });
        for item in selected.iter().filter(|item| item.mode() == Mode::Vm) {
            let plan = item
                .vm()
                .ok_or_else(|| Error::Invariant("VM plan missing".into()))?;
            for block in &plan.blocks {
                let va = image.moved[&block.old];
                regions.push(FrameRegion {
                    va,
                    len: THUNK_LEN as u32,
                    rows: vec![(0, entry_rule(8)), (6, entry_rule(16))],
                });
            }
        }
        for &(va, site, length) in &image.island_frames {
            let before = guest_rule(site.before)?;
            let after = guest_rule(site.after)?;
            let mut scratch128 = after.clone();
            scratch128.cfa_offset += 128;
            let mut scratch136 = after.clone();
            scratch136.cfa_offset += 136;
            let mut scratch144 = after.clone();
            scratch144.cfa_offset += 144;
            regions.push(FrameRegion {
                va,
                len: ISLAND_LEN as u32,
                rows: vec![
                    (0, stack_context_rule(16, 0)),
                    (8, before),
                    ((8 + length) as u32, after),
                    ((8 + length + 8) as u32, scratch128),
                    ((8 + length + 8 + 1) as u32, scratch136),
                    ((8 + length + 8 + 1 + 2) as u32, scratch144),
                    ((8 + length + 8 + 1 + 2 + 8) as u32, context_rule()),
                ],
            });
        }
        Ok(regions)
    }

    fn verify_fused(record: &[u8]) -> Result<()> {
        let code = record[0];
        let width = record[1];
        let dst = record[2];
        let src = record[3];
        let base = record[4];
        let index = record[5];
        let scale = record[6];
        let flags = record[7];
        let value = i64::from_le_bytes(record[8..16].try_into().unwrap());
        if !matches!(width, 1 | 2 | 4 | 8) || record[16..24] != [0; 8] || flags & !3 != 0 {
            return Err("invalid fused VM record".into());
        }
        let memory = matches!(code, VM_F_LOAD | VM_F_STORE);
        if memory {
            if !(base < 16 || base == 254 || base == 255)
                || !(index < 16 || index == 255)
                || !matches!(scale, 1 | 2 | 4 | 8)
                || base == 254 && (index != 255 || scale != 1)
            {
                return Err("invalid fused VM address".into());
            }
        } else if base != 255
            || index != 255
            || scale != 1
            || (code != VM_F_MOV_IR && src != 255 && value != 0)
        {
            return Err("invalid fused VM fields".into());
        }
        if (code == VM_F_STORE && dst != 0)
            || (code != VM_F_STORE && (dst >= 16 || flags & 1 != 0 && (dst >= 4 || width != 1)))
            || (src != 255 && (src >= 16 || flags & 2 != 0 && (src >= 4 || width != 1)))
            || (src == 255 && flags & 2 != 0)
            || (matches!(code, VM_F_MOV_IR | VM_F_LOAD) && src != 255)
            || (code == VM_F_MOV_RR && src == 255)
            || (code == VM_F_STORE && src == 255)
            || (code == VM_F_MOV_IR && flags & 2 != 0)
            || (code >= VM_F_ADD && src == 255 && flags & 2 != 0)
        {
            return Err("invalid fused VM register".into());
        }
        Ok(())
    }

    fn verify_record(record: &[u8], architecture: Architecture, blocks: usize) -> Result<u8> {
        if record.len() != OP_LEN {
            return Err("truncated VM record".into());
        }
        let code = record[0];
        if (VM_F_MOV_RR..=VM_F_TEST).contains(&code) {
            verify_fused(record)?;
            return Ok(code);
        }
        let (op, reg, base, index, scale, flags) = match architecture {
            Architecture::Stack => {
                if !(VM_PUSH_REG..=VM_SHIFT).contains(&code) || record[7] != 0 {
                    return Err("invalid stack VM opcode or reserved byte".into());
                }
                (code, record[2], record[3], record[4], record[5], record[6])
            }
            Architecture::Register => {
                if !(VM_R_READ_REG..=VM_R_SHIFT).contains(&code)
                    || record[2] >= 32
                    || record[3] >= 32
                {
                    return Err("invalid register VM opcode or temporary".into());
                }
                let op = code - VM_R_READ_REG + VM_PUSH_REG;
                let dst = record[2];
                let src = record[3];
                let unused = match op {
                    VM_PUSH_REG | VM_POP_REG | VM_CMOV_REG | VM_ADD..=VM_TEST => false,
                    VM_BSWAP | VM_SHIFT => src != 0,
                    VM_PUSH_IMM | VM_PUSH_MEM | VM_LEA | VM_PUSH_CC => src != 0,
                    VM_POP_MEM => dst != 0,
                    _ => dst != 0 || src != 0,
                };
                if unused {
                    return Err("nonzero unused VM register operand".into());
                }
                (
                    op,
                    if op == VM_PUSH_REG { src } else { dst },
                    record[4],
                    record[5],
                    record[6],
                    record[7],
                )
            }
        };
        let width = record[1];
        if (op <= VM_TEST && !matches!(width, 1 | 2 | 4 | 8))
            || (op == VM_CMOV_REG && !matches!(width, 2 | 4 | 8))
            || (op == VM_BSWAP && !matches!(width, 4 | 8))
            || (op == VM_SHIFT && !matches!(width, 1 | 2 | 4 | 8))
            || (op > VM_TEST && !matches!(op, VM_CMOV_REG | VM_BSWAP | VM_SHIFT) && width != 0)
        {
            return Err("invalid VM operand width".into());
        }
        let allowed_flags = match op {
            VM_PUSH_REG => 3,
            VM_PUSH_MEM => 2,
            VM_POP_REG => 1,
            VM_ADD | VM_SUB => VM_PRESERVE_CF | VM_USE_CF,
            VM_BXOR => VM_PRESERVE_FLAGS,
            VM_JCC | VM_PUSH_CC | VM_CMOV_REG => 15,
            VM_SHIFT => 7,
            _ => 0,
        };
        if flags & !allowed_flags != 0
            || matches!(op, VM_ADD | VM_SUB) && flags == (VM_PRESERVE_CF | VM_USE_CF)
            || op == VM_SHIFT && flags > VM_ROTATE_RIGHT
        {
            return Err("invalid VM operand flags".into());
        }
        if matches!(op, VM_PUSH_REG | VM_POP_REG | VM_CMOV_REG) {
            if reg >= 16 || (op != VM_CMOV_REG && flags & 1 != 0 && (reg >= 4 || width != 1)) {
                return Err("invalid VM guest register".into());
            }
        } else if architecture == Architecture::Stack && reg != 0 {
            return Err("nonzero unused VM guest register".into());
        }
        let value = i64::from_le_bytes(record[8..16].try_into().unwrap());
        if matches!(op, VM_PUSH_MEM | VM_POP_MEM | VM_LEA) {
            if !(base < 16 || base == 254 || base == 255)
                || !(index < 16 || index == 255)
                || !matches!(scale, 1 | 2 | 4 | 8)
                || (base == 254 && (index != 255 || scale != 1))
            {
                return Err("invalid VM address operand".into());
            }
        } else if base != 255
            || index != 255
            || scale != 1
            || (op == VM_SHIFT && !(1..i64::from(width * 8)).contains(&value))
            || (!matches!(op, VM_PUSH_IMM | VM_SHIFT) && value != 0)
        {
            return Err("nonzero unused VM address operand".into());
        }
        let target = i64::from_le_bytes(record[16..24].try_into().unwrap());
        if matches!(op, VM_JMP | VM_JCC) {
            if !(0..blocks as i64).contains(&target) {
                return Err("VM branch leaves bytecode".into());
            }
        } else if !matches!(op, VM_NATIVE | VM_TAIL) && target != 0 {
            return Err("nonzero unused VM target".into());
        }
        Ok(op)
    }

    pub(super) fn verify(
        binary: &elf::Binary,
        image: &VmImage,
        entries: &BTreeMap<u64, u64>,
        selected: &[Selected],
        seed: u64,
    ) -> Result<()> {
        if binary.content_from_virtual_address(image.runtime, image.code.len() as u64) != image.code
        {
            return Err(Error::Invariant("rewritten ELF changed VM region".into()));
        }
        for offset in runtime_offsets() {
            if offset >= runtime_len() {
                return Err("invalid VM runtime offset".into());
            }
        }
        for &va in &image.islands {
            if binary.content_from_virtual_address(va, 4) != ENDBR64 {
                return Err("VM native island lacks ENDBR64".into());
            }
        }
        let mut island_index = 0;
        for item in selected.iter().filter(|item| item.mode() == Mode::Vm) {
            let plan = item
                .vm()
                .ok_or_else(|| Error::Invariant("VM plan missing".into()))?;
            let codec = Codec::new(seed, item.function.start, plan.architecture);
            let order = permute_all(
                plan.blocks.len(),
                function_seed(seed ^ 0xb7e151628aed2a6b, item.function.start),
            );
            let relay_order = permute_all(
                plan.relays.len(),
                function_seed(seed ^ RELAY_SITE_SALT, item.function.start),
            );
            let mut pc = BTreeMap::new();
            let mut count = 0;
            for &index in &order {
                pc.insert(plan.blocks[index].old, count);
                count += plan.blocks[index].ops.len();
            }
            let mut relay_pc = vec![0; plan.relays.len()];
            for &index in &relay_order {
                relay_pc[index] = count;
                count += plan.relays[index].len();
            }
            if count != plan.op_count {
                return Err(Error::Invariant("VM operation count changed".into()));
            }
            let dispatch = dispatch(plan, &pc, &relay_pc, &codec)?;
            let mut addresses = None;
            for block in &plan.blocks {
                let thunk = image.moved[&block.old];
                if binary.content_from_virtual_address(thunk, 4) != ENDBR64 {
                    return Err("VM entry thunk lacks ENDBR64".into());
                }
                let meta = thunk + THUNK_LEN as u64;
                let metadata = binary.content_from_virtual_address(meta, META_LEN as u64);
                if metadata.len() != META_LEN {
                    return Err("truncated VM metadata".into());
                }
                let ops = meta
                    .checked_add_signed(i64::from_le_bytes(metadata[..8].try_into().unwrap()))
                    .ok_or("VM bytecode address overflow")?;
                let descriptor = meta
                    .checked_add_signed(i64::from_le_bytes(metadata[16..24].try_into().unwrap()))
                    .ok_or("VM descriptor address overflow")?;
                if descriptor & 7 != 0 || descriptor.checked_add(VM_CODEC_LEN as u64) != Some(ops) {
                    return Err("invalid VM descriptor placement".into());
                }
                let offset = descriptor
                    .checked_sub(image.runtime)
                    .ok_or("VM descriptor outside region")?;
                if offset < RUNTIME.len() as u64 {
                    return Err("VM descriptor overlaps runtime".into());
                }
                super::file_range(
                    image.code.len(),
                    offset,
                    (VM_CODEC_LEN + count * OP_LEN + dispatch.bytes.len()) as u64,
                )?;
                if addresses.is_some_and(|old| old != (ops, descriptor)) {
                    return Err("inconsistent VM descriptor references".into());
                }
                addresses = Some((ops, descriptor));
                if metadata
                    != encode_metadata(
                        ops as i64 - meta as i64,
                        pc[&block.old] as u32,
                        plan.op_count as u32,
                        descriptor as i64 - meta as i64,
                        plan.max_depth,
                    )
                {
                    return Err("VM metadata changed".into());
                }
            }
            let (ops, descriptor) =
                addresses.ok_or_else(|| Error::Invariant("empty VM plan".into()))?;
            if binary.content_from_virtual_address(descriptor, VM_CODEC_LEN as u64)
                != codec.descriptor(plan.blocks.len() + plan.relays.len(), count)?
            {
                return Err("VM encoding descriptor changed".into());
            }
            if binary.content_from_virtual_address(
                ops + (count * OP_LEN) as u64,
                dispatch.bytes.len() as u64,
            ) != dispatch.bytes
            {
                return Err("VM dispatch table changed".into());
            }
            let bytes = binary.content_from_virtual_address(ops, (count * OP_LEN) as u64);
            if bytes.len() != count * OP_LEN {
                return Err("truncated VM bytecode".into());
            }
            let mut position = 0;
            for records in order
                .iter()
                .map(|&index| plan.blocks[index].ops.as_slice())
                .chain(
                    relay_order
                        .iter()
                        .map(|&index| plan.relays[index].as_slice()),
                )
            {
                for op in records {
                    let at = ops + (position * OP_LEN) as u64;
                    let record = codec.decode_record(
                        &bytes[position * OP_LEN..(position + 1) * OP_LEN],
                        position,
                    )?;
                    verify_record(
                        &record,
                        plan.architecture,
                        plan.blocks.len() + plan.relays.len(),
                    )?;
                    let value = if op.base == 254 {
                        op.value - at as i64
                    } else {
                        op.value
                    };
                    let target = match op.target {
                        Target::None => 0,
                        Target::Block(_) | Target::Relay(_) => *dispatch
                            .tokens
                            .get(&op.target)
                            .ok_or_else(|| Error::Invariant("missing VM branch token".into()))?
                            as i64,
                        Target::Island(index) => {
                            *image
                                .islands
                                .get(island_index + index)
                                .ok_or_else(|| Error::Invariant("missing VM island".into()))?
                                as i64
                                - at as i64
                        }
                        Target::External(old) => {
                            let new = entries.get(&old).copied().unwrap_or(old);
                            if !executable_target(binary, new) {
                                return Err("VM tail target is not executable".into());
                            }
                            new as i64 - at as i64
                        }
                        Target::Abort => image.runtime as i64 + VM_ABORT_OFF as i64 - at as i64,
                    };
                    if record != serialize_op(op, plan.architecture, value, target) {
                        return Err("decoded VM record differs from plan".into());
                    }
                    position += 1;
                }
            }
            island_index += plan.islands.len();
        }
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::{
            FrameRegisterRule, RUNTIME, VM_POP_REG, VM_PUSH_IMM, VM_RETURN_OFF, VmImage, escape_ok,
            frame_depth, frame_regions, lift,
        };
        use iced_x86::{Decoder, DecoderOptions, Mnemonic};
        use std::collections::BTreeMap;

        fn instruction(bytes: &[u8]) -> iced_x86::Instruction {
            let mut decoder = Decoder::with_ip(64, bytes, 0x401000, DecoderOptions::NONE);
            let instruction = decoder.decode();
            assert!(!instruction.is_invalid() && !decoder.can_decode());
            instruction
        }

        #[test]
        fn lowers_simple_guest_stack_operations() {
            use super::{
                VM_LEA, VM_POP_MEM, VM_POP_REG, VM_PUSH_IMM, VM_PUSH_MEM, VM_PUSH_REG,
                lift_with_stack, register_ops,
            };
            let push = lift(&instruction(&[0x50])).unwrap().unwrap();
            assert_eq!(
                push.iter().map(|op| op.code).collect::<Vec<_>>(),
                [VM_PUSH_REG, VM_LEA, VM_POP_REG, VM_POP_MEM]
            );
            assert_eq!(
                (push[1].base, push[1].value, push[2].reg, push[3].base),
                (4, -8, 4, 4)
            );
            let pop = lift(&instruction(&[0x5b])).unwrap().unwrap();
            assert_eq!(
                pop.iter().map(|op| op.code).collect::<Vec<_>>(),
                [VM_PUSH_MEM, VM_LEA, VM_POP_REG, VM_POP_REG]
            );
            assert_eq!(
                (pop[0].base, pop[1].value, pop[2].reg, pop[3].reg),
                (4, 8, 4, 3)
            );
            let memory_push = lift(&instruction(&[0xff, 0x34, 0x24])).unwrap().unwrap();
            assert_eq!(
                memory_push.iter().map(|op| op.code).collect::<Vec<_>>(),
                [VM_PUSH_MEM, VM_LEA, VM_POP_REG, VM_POP_MEM]
            );
            assert_eq!((memory_push[0].base, memory_push[3].base), (4, 4));
            let memory_pop = lift(&instruction(&[0x8f, 0x04, 0x24])).unwrap().unwrap();
            assert_eq!(
                memory_pop.iter().map(|op| op.code).collect::<Vec<_>>(),
                [VM_PUSH_MEM, VM_LEA, VM_POP_REG, VM_POP_MEM]
            );
            assert_eq!((memory_pop[0].base, memory_pop[3].base), (4, 4));
            for bytes in [&[0x6a, 0xff][..], &[0x68, 0xff, 0xff, 0xff, 0xff][..]] {
                let ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!((ops[0].code, ops[0].value), (VM_PUSH_IMM, -1));
            }
            let registers: Vec<_> = (0..32).collect();
            for mut ops in [push, pop, memory_push, memory_pop] {
                register_ops(&mut ops, &registers).unwrap();
            }
            for bytes in [
                &[0x54][..],
                &[0x5c],
                &[0x66, 0x50],
                &[0x66, 0xff, 0x30],
                &[0x66, 0x8f, 0x00],
                &[0x9c],
            ] {
                assert!(lift(&instruction(bytes)).unwrap().is_none());
            }
            assert!(
                lift_with_stack(&instruction(&[0x50]), false, true, true, true)
                    .unwrap()
                    .is_none()
            );
        }

        #[test]
        fn register_xchg_reads_both_values_before_writing() {
            use super::{VM_POP_REG, VM_PUSH_REG, VM_R_READ_REG, VM_R_WRITE_REG, register_ops};
            let registers: Vec<_> = (0..32).collect();
            for (bytes, width) in [
                (&[0x86, 0xd8][..], 1),       // al, bl
                (&[0x86, 0xe0][..], 1),       // al, ah
                (&[0x66, 0x87, 0xd8][..], 2), // ax, bx
                (&[0x87, 0xd8][..], 4),       // eax, ebx
                (&[0x48, 0x87, 0xd8][..], 8), // rax, rbx
                (&[0x45, 0x87, 0xc8][..], 4), // r8d, r9d
                (&[0x87, 0xc0][..], 4),       // eax, eax still clears upper bits
            ] {
                let mut ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(
                    ops.iter().map(|op| (op.code, op.width)).collect::<Vec<_>>(),
                    [
                        (VM_PUSH_REG, width),
                        (VM_PUSH_REG, width),
                        (VM_POP_REG, width),
                        (VM_POP_REG, width),
                    ]
                );
                assert_eq!((ops[0].reg, ops[0].flags), (ops[2].reg, ops[2].flags));
                assert_eq!((ops[1].reg, ops[1].flags), (ops[3].reg, ops[3].flags));
                register_ops(&mut ops, &registers).unwrap();
                assert_eq!(
                    ops.iter().map(|op| op.code).collect::<Vec<_>>(),
                    [VM_R_READ_REG, VM_R_READ_REG, VM_R_WRITE_REG, VM_R_WRITE_REG]
                );
                assert_eq!(
                    (ops[0].dst, ops[1].dst, ops[2].src, ops[3].src),
                    (0, 1, 1, 0)
                );
            }
        }

        #[test]
        fn xchg_noops_and_memory_stay_distinct() {
            for bytes in [
                &[0x86, 0xc0][..],       // al, al
                &[0x66, 0x87, 0xc0][..], // ax, ax
                &[0x66, 0x90][..],       // alignment nop
                &[0x48, 0x87, 0xc0][..], // rax, rax
            ] {
                assert!(lift(&instruction(bytes)).unwrap().unwrap().is_empty());
            }
            for bytes in [
                &[0x48, 0x87, 0x18][..], // [rax], rbx is atomic
                &[0x48, 0x87, 0xe0][..], // rax, rsp
                &[0x87, 0xe0][..],       // eax, esp
                &[0x66, 0x87, 0xe0][..], // ax, sp
                &[0x40, 0x86, 0xe0][..], // al, spl
            ] {
                assert!(lift(&instruction(bytes)).unwrap().is_none());
            }
        }

        #[test]
        fn inc_dec_keep_carry_in_both_vm_architectures() {
            use super::{
                Architecture, VM_ADD, VM_BXOR, VM_PRESERVE_CF, VM_R_ADD, VM_R_SUB, VM_SUB, fuse,
                register_ops, serialize_op, verify_record,
            };
            for (bytes, width, opcode) in [
                (&[0xfe, 0xc0][..], 1, VM_ADD),       // inc al
                (&[0xfe, 0xcc][..], 1, VM_SUB),       // dec ah
                (&[0x66, 0xff, 0xc0][..], 2, VM_ADD), // inc ax
                (&[0xff, 0xc8][..], 4, VM_SUB),       // dec eax
                (&[0x48, 0xff, 0xc0][..], 8, VM_ADD), // inc rax
            ] {
                let ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(
                    (ops[1].value, ops[2].code, ops[2].width),
                    (1, opcode, width)
                );
                assert_eq!(ops[2].flags, VM_PRESERVE_CF);
                assert_eq!(fuse(&ops).len(), 4);
                let wire = serialize_op(&ops[2], Architecture::Stack, 0, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                let mut bad = wire;
                bad[6] = 3;
                assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                bad = wire;
                bad[0] = VM_BXOR;
                assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                let mut register_ops_code = ops;
                register_ops(&mut register_ops_code, &(0..32).collect::<Vec<_>>()).unwrap();
                assert_eq!(
                    register_ops_code[2].code,
                    if opcode == VM_ADD { VM_R_ADD } else { VM_R_SUB }
                );
                let wire = serialize_op(&register_ops_code[2], Architecture::Register, 0, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                let mut bad = wire;
                bad[7] = 3;
                assert!(verify_record(&bad, Architecture::Register, 1).is_err());
            }
            for bytes in [
                &[0x48, 0xff, 0xc4][..],
                &[0x48, 0xff, 0x00],
                &[0xf0, 0xff, 0x00],
            ] {
                assert!(lift(&instruction(bytes)).unwrap().is_none());
            }
        }

        #[test]
        fn adc_sbb_use_incoming_carry_without_fusion() {
            use super::{
                Architecture, VM_ADD, VM_R_ADD, VM_R_SUB, VM_SUB, VM_USE_CF, fuse, register_ops,
                serialize_op, verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for (bytes, width, code, register_code) in [
                (&[0x10, 0xc8][..], 1, VM_ADD, VM_R_ADD),
                (&[0x66, 0x11, 0xc8][..], 2, VM_ADD, VM_R_ADD),
                (&[0x11, 0xc8][..], 4, VM_ADD, VM_R_ADD),
                (&[0x48, 0x11, 0xc8][..], 8, VM_ADD, VM_R_ADD),
                (&[0x18, 0xc8][..], 1, VM_SUB, VM_R_SUB),
                (&[0x66, 0x19, 0xc8][..], 2, VM_SUB, VM_R_SUB),
                (&[0x19, 0xc8][..], 4, VM_SUB, VM_R_SUB),
                (&[0x48, 0x19, 0xc8][..], 8, VM_SUB, VM_R_SUB),
            ] {
                let mut ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(
                    (ops[2].code, ops[2].width, ops[2].flags),
                    (code, width, VM_USE_CF)
                );
                assert_eq!(fuse(&ops).len(), 4);
                let wire = serialize_op(&ops[2], Architecture::Stack, 0, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                for flags in [3, 4] {
                    let mut bad = wire;
                    bad[6] = flags;
                    assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                }
                register_ops(&mut ops, &registers).unwrap();
                assert_eq!((ops[2].code, ops[2].flags), (register_code, VM_USE_CF));
                let wire = serialize_op(&ops[2], Architecture::Register, 0, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                for flags in [3, 4] {
                    let mut bad = wire;
                    bad[7] = flags;
                    assert!(verify_record(&bad, Architecture::Register, 1).is_err());
                }
            }
            for bytes in [&[0x11, 0x08][..], &[0x13, 0x08], &[0x83, 0xd0, 0xff]] {
                assert_eq!(
                    lift(&instruction(bytes)).unwrap().unwrap()[2].flags,
                    VM_USE_CF
                );
            }
            assert!(lift(&instruction(&[0xf0, 0x11, 0x08])).unwrap().is_none());
        }

        #[test]
        fn neg_not_lower_with_distinct_flag_rules() {
            use super::{
                Architecture, VM_BXOR, VM_POP_REG, VM_PRESERVE_FLAGS, VM_PUSH_IMM, VM_PUSH_REG,
                VM_R_SUB, VM_R_XOR, VM_SUB, fuse, lift_with_stack, register_ops, serialize_op,
                verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for (bytes, width, code, register_code, mode) in [
                (&[0xf6, 0xd8][..], 1, VM_SUB, VM_R_SUB, 0),
                (&[0x66, 0xf7, 0xd8][..], 2, VM_SUB, VM_R_SUB, 0),
                (&[0xf7, 0xd8][..], 4, VM_SUB, VM_R_SUB, 0),
                (&[0x48, 0xf7, 0xd8][..], 8, VM_SUB, VM_R_SUB, 0),
                (&[0xf6, 0xd0][..], 1, VM_BXOR, VM_R_XOR, VM_PRESERVE_FLAGS),
                (
                    &[0x66, 0xf7, 0xd0][..],
                    2,
                    VM_BXOR,
                    VM_R_XOR,
                    VM_PRESERVE_FLAGS,
                ),
                (&[0xf7, 0xd0][..], 4, VM_BXOR, VM_R_XOR, VM_PRESERVE_FLAGS),
                (
                    &[0x48, 0xf7, 0xd0][..],
                    8,
                    VM_BXOR,
                    VM_R_XOR,
                    VM_PRESERVE_FLAGS,
                ),
            ] {
                let mut ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(ops.len(), 4);
                assert_eq!(
                    (ops[2].code, ops[2].width, ops[2].flags),
                    (code, width, mode)
                );
                assert_eq!(ops[3].code, VM_POP_REG);
                assert_eq!(fuse(&ops).len(), 4);
                if code == VM_SUB {
                    assert_eq!(
                        (ops[0].code, ops[0].value, ops[1].code),
                        (VM_PUSH_IMM, 0, VM_PUSH_REG)
                    );
                } else {
                    assert_eq!(
                        (ops[0].code, ops[1].code, ops[1].value),
                        (VM_PUSH_REG, VM_PUSH_IMM, -1)
                    );
                }
                let wire = serialize_op(&ops[2], Architecture::Stack, 0, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                let invalid_flags: &[u8] = if code == VM_SUB {
                    &[3, 4, 5]
                } else {
                    &[1, 2, 3, 5]
                };
                for &invalid in invalid_flags {
                    let mut bad = wire;
                    bad[6] = invalid;
                    assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                }
                register_ops(&mut ops, &registers).unwrap();
                assert_eq!((ops[2].code, ops[2].flags), (register_code, mode));
                let wire = serialize_op(&ops[2], Architecture::Register, 0, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                let mut bad = wire;
                bad[7] = 5;
                assert!(verify_record(&bad, Architecture::Register, 1).is_err());
            }
            for (bytes, expected) in [(&[0xf6, 0xdc][..], VM_SUB), (&[0xf6, 0xd4], VM_BXOR)] {
                let ops = lift(&instruction(bytes)).unwrap().unwrap();
                let source = if expected == VM_SUB { &ops[1] } else { &ops[0] };
                assert_eq!(
                    (ops[2].code, source.reg, source.flags, ops[3].flags),
                    (expected, 0, 1, 1)
                );
            }
            for bytes in [&[0xf7, 0x18][..], &[0xf7, 0x10]] {
                let ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!((ops[3].code, ops[3].width), (super::VM_POP_MEM, 4));
            }
            for bytes in [
                &[0xf0, 0xf7, 0x18][..],
                &[0xf0, 0xf7, 0x10],
                &[0x48, 0xf7, 0xdc],
                &[0x48, 0xf7, 0xd4],
            ] {
                assert!(lift(&instruction(bytes)).unwrap().is_none());
            }
            assert!(
                lift_with_stack(&instruction(&[0xf7, 0xd8]), true, true, true, false)
                    .unwrap()
                    .is_none()
            );
        }

        #[test]
        fn bswap_keeps_flags_and_rejects_undefined_width() {
            use super::{
                Architecture, VM_BSWAP, VM_POP_REG, VM_PUSH_REG, VM_R_BSWAP, VM_R_READ_REG,
                VM_R_WRITE_REG, fuse, lift_with_stack, register_ops, serialize_op, verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for (bytes, width, guest) in [
                (&[0x0f, 0xc8][..], 4, 0),
                (&[0x48, 0x0f, 0xc8][..], 8, 0),
                (&[0x49, 0x0f, 0xc8][..], 8, 8),
            ] {
                let mut ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(
                    ops.iter().map(|op| (op.code, op.width)).collect::<Vec<_>>(),
                    [(VM_PUSH_REG, width), (VM_BSWAP, width), (VM_POP_REG, width)]
                );
                assert_eq!((ops[0].reg, ops[2].reg, ops[1].flags), (guest, guest, 0));
                assert_eq!(fuse(&ops).len(), 3);
                let wire = serialize_op(&ops[1], Architecture::Stack, 0, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                for (at, value) in [(1, 2), (2, 1), (3, 0), (6, 1), (7, 1), (8, 1), (16, 1)] {
                    let mut bad = wire;
                    bad[at] = value;
                    assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                }
                register_ops(&mut ops, &registers).unwrap();
                assert_eq!(
                    ops.iter().map(|op| op.code).collect::<Vec<_>>(),
                    [VM_R_READ_REG, VM_R_BSWAP, VM_R_WRITE_REG]
                );
                assert_eq!(
                    (ops[0].dst, ops[1].dst, ops[1].src, ops[2].src),
                    (0, 0, 0, 0)
                );
                let wire = serialize_op(&ops[1], Architecture::Register, 0, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                for (at, value) in [(1, 2), (2, 32), (3, 1), (4, 0), (7, 1), (8, 1), (16, 1)] {
                    let mut bad = wire;
                    bad[at] = value;
                    assert!(verify_record(&bad, Architecture::Register, 1).is_err());
                }
            }
            assert!(lift(&instruction(&[0x48, 0x0f, 0xcc])).unwrap().is_none());
            for bytes in [&[0x66, 0x0f, 0xc8][..], &[0xf0, 0x0f, 0xc8]] {
                let mut decoder = iced_x86::Decoder::new(64, bytes, iced_x86::DecoderOptions::NONE);
                let instruction = decoder.decode();
                assert!(instruction.is_invalid() || lift(&instruction).unwrap().is_none());
            }
            assert!(
                lift_with_stack(&instruction(&[0x0f, 0xc8]), true, true, true, false)
                    .unwrap()
                    .is_none()
            );
        }

        #[test]
        fn immediate_shifts_and_rotates_encode_both_architectures() {
            use super::{
                Architecture, VM_POP_REG, VM_PUSH_REG, VM_R_READ_REG, VM_R_SHIFT, VM_R_WRITE_REG,
                VM_ROTATE_LEFT, VM_ROTATE_RIGHT, VM_SHIFT, VM_SHIFT_ARITH, VM_SHIFT_LEFT,
                VM_SHIFT_RIGHT, register_ops, serialize_op, verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for (bytes, width, mode, count) in [
                (&[0xd0, 0xe0][..], 1, VM_SHIFT_LEFT, 1),
                (&[0xd0, 0xec][..], 1, VM_SHIFT_RIGHT, 1),
                (&[0x66, 0xc1, 0xf8, 0x03][..], 2, VM_SHIFT_ARITH, 3),
                (&[0xc1, 0xe0, 0x04][..], 4, VM_SHIFT_LEFT, 4),
                (&[0x49, 0xc1, 0xe8, 0x3f][..], 8, VM_SHIFT_RIGHT, 63),
                (&[0x41, 0xc1, 0xf8, 0x1f][..], 4, VM_SHIFT_ARITH, 31),
                (&[0xc1, 0xe0, 0x21][..], 4, VM_SHIFT_LEFT, 1),
                (&[0xd0, 0xc0][..], 1, VM_ROTATE_LEFT, 1),
                (&[0xd0, 0xcc][..], 1, VM_ROTATE_RIGHT, 1),
                (&[0x66, 0xc1, 0xc0, 0x03][..], 2, VM_ROTATE_LEFT, 3),
                (&[0xc1, 0xc8, 0x04][..], 4, VM_ROTATE_RIGHT, 4),
                (&[0x48, 0xc1, 0xc0, 0x3f][..], 8, VM_ROTATE_LEFT, 63),
                (&[0x49, 0xc1, 0xc8, 0x3f][..], 8, VM_ROTATE_RIGHT, 63),
                (&[0xc1, 0xc8, 0x21][..], 4, VM_ROTATE_RIGHT, 1),
            ] {
                let mut ops = lift(&instruction(bytes)).unwrap().unwrap();
                assert_eq!(
                    ops.iter().map(|op| op.code).collect::<Vec<_>>(),
                    [VM_PUSH_REG, VM_SHIFT, VM_POP_REG]
                );
                assert_eq!(
                    (ops[1].width, ops[1].flags, ops[1].value),
                    (width, mode, count)
                );
                let wire = serialize_op(&ops[1], Architecture::Stack, ops[1].value, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                register_ops(&mut ops, &registers).unwrap();
                assert_eq!(
                    ops.iter().map(|op| op.code).collect::<Vec<_>>(),
                    [VM_R_READ_REG, VM_R_SHIFT, VM_R_WRITE_REG]
                );
                assert_eq!((ops[0].dst, ops[1].dst, ops[2].src), (0, 0, 0));
                let wire = serialize_op(&ops[1], Architecture::Register, ops[1].value, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
            }
        }

        #[test]
        fn immediate_bit_ops_reject_unsafe_counts_and_records() {
            use super::{Architecture, VM_R_SHIFT, VM_SHIFT, serialize_op, verify_record};
            for bytes in [
                &[0xc1, 0xe0, 0x20][..],       // masked count zero
                &[0xc0, 0xe0, 0x08][..],       // count reaches byte width
                &[0x66, 0xc1, 0xe8, 0x10][..], // count reaches word width
                &[0xd3, 0xe0][..],             // CL count
                &[0xc1, 0x20, 0x01][..],       // memory destination
                &[0x48, 0xc1, 0xe4, 0x01][..], // RSP destination
                &[0xc1, 0xc0, 0x20][..],       // masked rotate count zero
                &[0xc0, 0xc8, 0x08][..],       // rotate count reaches byte width
                &[0x66, 0xc1, 0xc0, 0x10][..], // rotate count reaches word width
                &[0xd3, 0xc0][..],             // CL rotate count
                &[0xd1, 0x08][..],             // memory rotate
                &[0x48, 0xd1, 0xc4][..],       // RSP rotate
                &[0xd0, 0xd0][..],             // RCL
                &[0xd0, 0xd8][..],             // RCR
            ] {
                assert!(lift(&instruction(bytes)).unwrap().is_none());
            }
            let mut ops = lift(&instruction(&[0xc1, 0xe0, 0x04])).unwrap().unwrap();
            for architecture in [Architecture::Stack, Architecture::Register] {
                if architecture == Architecture::Register {
                    super::register_ops(&mut ops, &(0..32).collect::<Vec<_>>()).unwrap();
                }
                let mut wire = serialize_op(&ops[1], architecture, ops[1].value, 0);
                assert_eq!(
                    wire[0],
                    if architecture == Architecture::Stack {
                        VM_SHIFT
                    } else {
                        VM_R_SHIFT
                    }
                );
                let mode_at = if architecture == Architecture::Stack {
                    6
                } else {
                    7
                };
                let unused_at = if architecture == Architecture::Stack {
                    2
                } else {
                    3
                };
                for (at, value) in [
                    (1, 0),
                    (mode_at, 5),
                    (unused_at, 1),
                    (8, 0),
                    (8, 32),
                    (16, 1),
                ] {
                    let old = wire[at];
                    wire[at] = value;
                    assert!(verify_record(&wire, architecture, 1).is_err());
                    wire[at] = old;
                }
            }
        }

        #[test]
        fn setcc_uses_existing_byte_stores() {
            use super::{
                Architecture, VM_POP_MEM, VM_POP_REG, VM_PUSH_CC, VM_R_CC, VM_R_WRITE_REG,
                lift_with_stack, register_ops, serialize_op, verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for condition in 0..16 {
                let bytes = [0x0f, 0x90 + condition, 0xc0];
                let ops = lift(&instruction(&bytes)).unwrap().unwrap();
                assert_eq!(
                    (ops[0].code, ops[0].flags, ops[1].code),
                    (VM_PUSH_CC, condition, VM_POP_REG)
                );
                assert_eq!(ops[1].width, 1);
                let wire = serialize_op(&ops[0], Architecture::Stack, 0, 0);
                assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                for (at, value) in [(1, 1), (3, 0), (6, 16), (8, 1), (16, 1)] {
                    let mut bad = wire;
                    bad[at] = value;
                    assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
                }
                let mut converted = ops;
                register_ops(&mut converted, &registers).unwrap();
                assert_eq!(
                    (converted[0].code, converted[1].code),
                    (VM_R_CC, VM_R_WRITE_REG)
                );
                let wire = serialize_op(&converted[0], Architecture::Register, 0, 0);
                assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                for (at, value) in [(1, 1), (3, 1), (7, 16), (8, 1), (16, 1)] {
                    let mut bad = wire;
                    bad[at] = value;
                    assert!(verify_record(&bad, Architecture::Register, 1).is_err());
                }
            }
            let high = lift(&instruction(&[0x0f, 0x94, 0xc4])).unwrap().unwrap();
            assert_eq!((high[1].reg, high[1].flags), (0, 1));
            let memory = lift(&instruction(&[0x0f, 0x95, 0x04, 0x24]))
                .unwrap()
                .unwrap();
            assert_eq!(
                (memory[1].code, memory[1].width, memory[1].base),
                (VM_POP_MEM, 1, 4)
            );
            assert!(
                lift_with_stack(&instruction(&[0x0f, 0x94, 0xc0]), true, false, true, true)
                    .unwrap()
                    .is_none()
            );
            for bytes in [&[0x64, 0x0f, 0x94, 0x00][..], &[0x67, 0x0f, 0x94, 0x00]] {
                assert!(lift(&instruction(bytes)).is_err());
            }
        }

        #[test]
        fn cmov_reads_before_condition_and_validates_both_formats() {
            use super::{
                Architecture, VM_CMOV_REG, VM_PUSH_MEM, VM_PUSH_REG, VM_R_CMOV_REG, VM_R_LOAD,
                VM_R_READ_REG, lift_with_stack, register_ops, serialize_op, verify_record,
            };
            let registers: Vec<_> = (0..32).collect();
            for condition in 0..16 {
                for (prefix, width) in [(&[][..], 4), (&[0x66][..], 2), (&[0x48][..], 8)] {
                    let mut bytes = prefix.to_vec();
                    bytes.extend_from_slice(&[0x0f, 0x40 + condition, 0xc1]);
                    let ops = lift(&instruction(&bytes)).unwrap().unwrap();
                    assert_eq!(
                        (ops[0].code, ops[1].code, ops[1].width, ops[1].flags),
                        (VM_PUSH_REG, VM_CMOV_REG, width, condition)
                    );
                    let wire = serialize_op(&ops[1], Architecture::Stack, 0, 0);
                    assert!(verify_record(&wire, Architecture::Stack, 1).is_ok());
                    let mut converted = ops;
                    register_ops(&mut converted, &registers).unwrap();
                    assert_eq!(
                        (converted[0].code, converted[1].code),
                        (VM_R_READ_REG, VM_R_CMOV_REG)
                    );
                    let wire = serialize_op(&converted[1], Architecture::Register, 0, 0);
                    assert!(verify_record(&wire, Architecture::Register, 1).is_ok());
                }
            }
            let ops = lift(&instruction(&[0x0f, 0x45, 0x00])).unwrap().unwrap();
            assert_eq!((ops[0].code, ops[1].code), (VM_PUSH_MEM, VM_CMOV_REG));
            let mut converted = ops;
            register_ops(&mut converted, &registers).unwrap();
            assert_eq!(
                (converted[0].code, converted[1].code),
                (VM_R_LOAD, VM_R_CMOV_REG)
            );
            let op = lift(&instruction(&[0x0f, 0x44, 0xc1])).unwrap().unwrap()[1];
            let wire = serialize_op(&op, Architecture::Stack, 0, 0);
            for (at, value) in [(1, 1), (2, 16), (3, 0), (6, 16), (7, 1), (8, 1), (16, 1)] {
                let mut bad = wire;
                bad[at] = value;
                assert!(verify_record(&bad, Architecture::Stack, 1).is_err());
            }
            let mut converted = lift(&instruction(&[0x0f, 0x44, 0xc1])).unwrap().unwrap();
            register_ops(&mut converted, &registers).unwrap();
            let wire = serialize_op(&converted[1], Architecture::Register, 0, 0);
            for (at, value) in [(1, 1), (2, 16), (3, 32), (4, 0), (7, 16), (8, 1), (16, 1)] {
                let mut bad = wire;
                bad[at] = value;
                assert!(verify_record(&bad, Architecture::Register, 1).is_err());
            }
            assert!(
                lift_with_stack(&instruction(&[0x0f, 0x44, 0xc1]), true, true, false, true)
                    .unwrap()
                    .is_none()
            );
            assert!(
                lift(&instruction(&[0x48, 0x0f, 0x44, 0xe1]))
                    .unwrap()
                    .is_none()
            );
            for bytes in [&[0x64, 0x0f, 0x44, 0x00][..], &[0x67, 0x0f, 0x44, 0x00]] {
                assert!(lift(&instruction(bytes)).is_err());
            }
        }

        #[test]
        fn plt_veneer_requires_a_direct_got_jump() {
            use super::plt_slot;
            assert_eq!(plt_slot(&[0xff, 0x25, 0x10, 0, 0, 0], 0x1000), Some(0x1016));
            assert_eq!(
                plt_slot(
                    &[0xf3, 0x0f, 0x1e, 0xfa, 0xf2, 0xff, 0x25, 0, 0, 0, 0],
                    0x2000
                ),
                Some(0x200b)
            );
            assert_eq!(plt_slot(&[0xff, 0x15, 0, 0, 0, 0], 0x1000), None);
            assert_eq!(plt_slot(&[0xff, 0x25, 0], 0x1000), None);
            assert_eq!(plt_slot(&[0xff, 0x25, 0, 0, 0, 0], u64::MAX), None);
        }

        #[test]
        fn fusion_covers_moves_arithmetic_and_comparisons() {
            use super::{
                VM_F_ADD, VM_F_CMP, VM_F_LOAD, VM_F_MOV_IR, VM_F_MOV_RR, VM_F_STORE, fuse, lift,
            };
            for (bytes, code) in [
                (&[0x48, 0x89, 0xd8][..], VM_F_MOV_RR),
                (&[0xb8, 0x34, 0x12, 0, 0][..], VM_F_MOV_IR),
                (&[0x48, 0x8b, 0x05, 0, 0, 0, 0][..], VM_F_LOAD),
                (&[0x48, 0x89, 0x18][..], VM_F_STORE),
                (&[0x83, 0xc0, 0x03][..], VM_F_ADD),
                (&[0x48, 0x39, 0xd8][..], VM_F_CMP),
            ] {
                let lowered = lift(&instruction(bytes)).unwrap().unwrap();
                let fused = fuse(&lowered);
                assert_eq!(fused.len(), 1);
                assert_eq!(fused[0].code, code);
            }
            let high = fuse(&lift(&instruction(&[0x88, 0xe0])).unwrap().unwrap());
            assert_eq!(high[0].code, VM_F_MOV_RR);
            assert_eq!(high[0].flags, 2);
            let signed = lift(&instruction(&[0x48, 0x0f, 0xbe, 0xc4]))
                .unwrap()
                .unwrap();
            assert_eq!(fuse(&signed).len(), 2);
        }

        #[test]
        fn fused_record_validation_rejects_bad_fields() {
            use super::{
                Architecture, Op, VM_F_ADD, VM_F_LOAD, VM_F_MOV_RR, serialize_op, verify_record,
            };
            let mut op = Op::new(VM_F_MOV_RR, 1);
            op.dst = 0;
            op.src = 3;
            op.flags = 2;
            let good = serialize_op(&op, Architecture::Stack, 0, 0);
            for arch in [Architecture::Stack, Architecture::Register] {
                assert!(verify_record(&good, arch, 1).is_ok());
                for (at, value) in [(1, 3), (3, 255), (3, 16), (5, 0), (7, 4), (16, 1)] {
                    let mut bad = good;
                    bad[at] = value;
                    assert!(verify_record(&bad, arch, 1).is_err(), "{at}: {value}");
                }
                let mut add = Op::new(VM_F_ADD, 4);
                add.dst = 0;
                add.src = 255;
                add.value = -1;
                assert!(verify_record(&serialize_op(&add, arch, -1, 0), arch, 1).is_ok());
                let mut load = Op::new(VM_F_LOAD, 8);
                load.base = 254;
                load.src = 255;
                assert!(verify_record(&serialize_op(&load, arch, -7, 0), arch, 1).is_ok());
            }
        }

        #[test]
        fn tail_records_use_a_relative_target_in_both_architectures() {
            use super::{Architecture, Op, VM_R_TAIL, VM_TAIL, serialize_op, verify_record};
            for (architecture, code) in [
                (Architecture::Stack, VM_TAIL),
                (Architecture::Register, VM_R_TAIL),
            ] {
                let record = serialize_op(&Op::new(code, 0), architecture, 0, -43);
                assert_eq!(verify_record(&record, architecture, 1).unwrap(), VM_TAIL);
                for at in [1, 2, 4, 7, 8] {
                    let mut malformed = record;
                    malformed[at] = 1;
                    assert!(verify_record(&malformed, architecture, 1).is_err());
                }
            }
        }

        #[test]
        fn codec_maps_only_its_architecture_and_replays_records() {
            use super::{Architecture, Codec, OP_LEN, mask_record};
            for seed in [0, 1, u64::MAX, 0x83ac0195e27d6b4f] {
                for architecture in [Architecture::Stack, Architecture::Register] {
                    let codec = Codec::new(seed, 0x401137, architecture);
                    assert_ne!(
                        codec.descriptor(1, 1).unwrap(),
                        Codec::new(seed, 0x401138, architecture)
                            .descriptor(1, 1)
                            .unwrap()
                    );
                    assert_ne!(
                        codec.descriptor(1, 1).unwrap(),
                        Codec::new(seed ^ 1, 0x401137, architecture)
                            .descriptor(1, 1)
                            .unwrap()
                    );
                    let mut header = codec.header;
                    header.sort_unstable();
                    assert_eq!(header, [0, 1, 2, 3, 4, 5, 6, 7]);
                    let mut words = codec.words;
                    words.sort_unstable();
                    assert_eq!(words, [0, 1, 2]);
                    assert_eq!(
                        (0..=255).filter(|&code| codec.valid_opcode(code)).count(),
                        33
                    );
                    for opcode in 0..=255 {
                        assert_eq!(codec.opcode(codec.opcode(opcode, false), true), opcode);
                        let mut plain = [0x95; OP_LEN];
                        plain[0] = opcode;
                        if !codec.valid_opcode(opcode) {
                            assert!(codec.encode_record(plain, 7).is_err());
                            continue;
                        }
                        for pc in [0, 1, 65534] {
                            let cipher = codec.encode_record(plain, pc).unwrap();
                            assert_ne!(cipher, plain);
                            assert_ne!(cipher, codec.encode_record(plain, pc + 1).unwrap());
                            assert_eq!(codec.decode_record(&cipher, pc).unwrap(), plain);
                        }
                    }
                    assert!(codec.encode_record([0; OP_LEN], 0).is_err());
                    assert!(codec.decode_record(&[0; OP_LEN - 1], 0).is_err());
                    let mut plain = [0; OP_LEN];
                    plain[0] = if architecture == Architecture::Stack {
                        super::VM_PUSH_REG
                    } else {
                        super::VM_R_READ_REG
                    };
                    let mut invalid = codec.encode_record(plain, 7).unwrap();
                    mask_record(&mut invalid, codec.key, 7);
                    invalid[codec.words[0] as usize * 8 + codec.header[0] as usize] =
                        codec.opcode(0, false);
                    mask_record(&mut invalid, codec.key, 7);
                    assert!(codec.decode_record(&invalid, 7).is_err());
                }
            }
        }

        #[test]
        fn codec_matches_fixed_vectors() {
            use super::{Architecture, Codec, Op, serialize_op};
            for (architecture, code, pc, value, expected) in [
                (
                    Architecture::Register,
                    super::VM_R_READ_REG,
                    37,
                    -17,
                    [
                        227, 75, 25, 95, 99, 2, 224, 233, 250, 48, 218, 185, 224, 77, 67, 46, 84,
                        136, 176, 147, 240, 81, 32, 159,
                    ],
                ),
                (
                    Architecture::Stack,
                    super::VM_PUSH_MEM,
                    65534,
                    -4096,
                    [
                        246, 52, 176, 79, 13, 233, 51, 119, 227, 14, 69, 170, 235, 120, 127, 26,
                        234, 101, 211, 78, 85, 198, 123, 122,
                    ],
                ),
            ] {
                let codec = Codec::new(0, 0x401137, architecture);
                let mut op = Op::new(
                    code,
                    if architecture == Architecture::Register {
                        1
                    } else {
                        8
                    },
                );
                if architecture == Architecture::Register {
                    op.dst = 29;
                    op.src = 3;
                    op.flags = 3;
                } else {
                    op.base = 254;
                    op.flags = 2;
                }
                let plain = serialize_op(&op, architecture, value, 0);
                let cipher = codec.encode_record(plain, pc).unwrap();
                assert_eq!(cipher, expected);
                assert_eq!(codec.decode_record(&expected, pc).unwrap(), plain);
            }
        }

        #[test]
        fn architecture_and_interpreter_variants_are_selected() {
            use super::{Architecture, Codec, VM_CODEC_VARIANT};
            let choices: Vec<_> = (0..32)
                .map(|seed| Architecture::select(seed, 0x401000))
                .collect();
            assert!(choices.contains(&Architecture::Stack));
            assert!(choices.contains(&Architecture::Register));
            let variants: Vec<_> = (0..32).map(|seed| Codec::variant(seed, 0x401000)).collect();
            assert!(variants.contains(&0));
            assert!(variants.contains(&1));
            for seed in [0, 1, u64::MAX] {
                let variant = Codec::variant(seed, 0x401000);
                assert_eq!(
                    Codec::new(seed, 0x401000, Architecture::Stack)
                        .descriptor(1, 1)
                        .unwrap()[VM_CODEC_VARIANT],
                    variant
                );
                assert_eq!(
                    Codec::new(seed, 0x401000, Architecture::Register)
                        .descriptor(1, 1)
                        .unwrap()[VM_CODEC_VARIANT],
                    variant
                );
            }
        }

        #[test]
        fn branch_tokens_resolve_to_distinct_block_starts() {
            use super::{
                Architecture, Codec, Op, VM_CODEC_BLOCKS, VM_CODEC_TABLE, VM_JMP, VmBlock, VmPlan,
                dispatch, verify_record,
            };
            let plan = VmPlan {
                architecture: Architecture::Stack,
                blocks: [0x10, 0x20, 0x30]
                    .into_iter()
                    .zip([2, 3, 1])
                    .map(|(old, count)| VmBlock {
                        old,
                        ops: vec![Op::new(VM_JMP, 0); count],
                    })
                    .collect(),
                relays: Vec::new(),
                islands: Vec::new(),
                op_count: 6,
                max_depth: 0,
            };
            let starts = BTreeMap::from([(0x10, 0), (0x20, 2), (0x30, 5)]);
            for seed in [0, 1, u64::MAX] {
                let codec = Codec::new(seed, 0x401000, Architecture::Stack);
                let table = dispatch(&plan, &starts, &[], &codec).unwrap();
                assert_eq!(table.bytes.len(), 12);
                assert_eq!(
                    table
                        .tokens
                        .values()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>(),
                    (0..3).collect()
                );
                assert_eq!(
                    table.bytes,
                    dispatch(&plan, &starts, &[], &codec).unwrap().bytes
                );
                let descriptor = codec.descriptor(3, 6).unwrap();
                assert!(codec.descriptor(u16::MAX as usize + 1, 6).is_err());
                assert_eq!(
                    &descriptor[VM_CODEC_BLOCKS..VM_CODEC_BLOCKS + 2],
                    &3u16.to_le_bytes()
                );
                assert_eq!(
                    &descriptor[VM_CODEC_TABLE..VM_CODEC_TABLE + 4],
                    &144u32.to_le_bytes()
                );
                let branch = Op::new(VM_JMP, 0);
                for (token, valid) in [(-1, false), (0, true), (2, true), (3, false)] {
                    assert_eq!(
                        verify_record(
                            &super::serialize_op(&branch, Architecture::Stack, 0, token),
                            Architecture::Stack,
                            3
                        )
                        .is_ok(),
                        valid
                    );
                }
            }
        }

        #[test]
        fn relay_paths_reconverge_and_respect_the_operation_limit() {
            use super::{
                Architecture, Op, Target, VM_F_MOV_RR, VM_JCC, VM_JMP, VM_R_JCC, VM_R_JMP, VM_RET,
                VmBlock, VmPlan,
            };
            let make_plan = || {
                let mut blocks = Vec::new();
                for old in [0x10, 0x20, 0x30] {
                    let mut jump = Op::new(VM_JMP, 0);
                    jump.target = Target::Block(0x40);
                    blocks.push(VmBlock {
                        old,
                        ops: vec![jump],
                    });
                }
                blocks.push(VmBlock {
                    old: 0x40,
                    ops: vec![Op::new(VM_RET, 0)],
                });
                VmPlan {
                    architecture: Architecture::Stack,
                    blocks,
                    relays: Vec::new(),
                    islands: Vec::new(),
                    op_count: 4,
                    max_depth: 0,
                }
            };
            for seed in [0, 1, u64::MAX] {
                let mut plan = make_plan();
                plan.choose_architecture(seed, 0x401000).unwrap();
                let (jmp, jcc) = match plan.architecture {
                    Architecture::Stack => (VM_JMP, VM_JCC),
                    Architecture::Register => (VM_R_JMP, VM_R_JCC),
                };
                assert_eq!((plan.relays.len(), plan.op_count), (4, 12));
                for block in plan.blocks.iter().filter(|block| block.ops.len() == 2) {
                    let Target::Relay(a) = block.ops[0].target else {
                        panic!("missing first relay")
                    };
                    assert!(matches!(block.ops[1].target, Target::Relay(b) if b == a + 1));
                    assert_eq!((block.ops[0].code, block.ops[1].code), (jcc, jmp));
                    assert_eq!(plan.relays[a].len(), 1);
                    assert_eq!(plan.relays[a + 1].len(), 2);
                    for op in plan.relays[a].iter().chain(&plan.relays[a + 1]) {
                        assert!(matches!(op.target, Target::Block(0x40)));
                        assert!(matches!(op.code, code if code == jmp || code == jcc));
                    }
                }
                let mut replay = make_plan();
                replay.choose_architecture(seed, 0x401000).unwrap();
                assert_eq!(
                    plan.blocks
                        .iter()
                        .map(|block| block.ops.len())
                        .collect::<Vec<_>>(),
                    replay
                        .blocks
                        .iter()
                        .map(|block| block.ops.len())
                        .collect::<Vec<_>>()
                );
            }
            let mut full = make_plan();
            let mut identity = Op::new(VM_F_MOV_RR, 8);
            identity.src = 0;
            identity.dst = 0;
            full.blocks[0].ops.splice(0..0, vec![identity; 65531]);
            full.op_count = 65535;
            full.choose_architecture(0, 0x401000).unwrap();
            assert!(full.relays.is_empty());
        }

        #[test]
        fn register_conversion_names_operands_and_rejects_live_exits() {
            use super::{
                Op, VM_ADD, VM_CMP, VM_NATIVE, VM_PUSH_REG, VM_R_ADD, VM_R_WRITE_REG, register_ops,
            };
            let registers: Vec<_> = (0..32).rev().collect();
            let mut read = Op::new(VM_PUSH_REG, 8);
            read.reg = 15;
            let mut write = Op::new(VM_POP_REG, 8);
            write.reg = 0;
            let mut ops = vec![read, Op::new(VM_PUSH_IMM, 8), Op::new(VM_ADD, 8), write];
            register_ops(&mut ops, &registers).unwrap();
            assert_eq!((ops[0].dst, ops[0].src), (31, 15));
            assert_eq!((ops[1].dst, ops[2].dst, ops[2].src), (30, 31, 30));
            assert_eq!((ops[2].code, ops[3].code), (VM_R_ADD, VM_R_WRITE_REG));
            assert_eq!((ops[3].dst, ops[3].src), (0, 31));
            let mut comparison = vec![read, read, Op::new(VM_CMP, 8), Op::new(VM_NATIVE, 0)];
            register_ops(&mut comparison, &registers).unwrap();
            for mut invalid in [
                vec![read],
                vec![write],
                vec![read, Op::new(VM_NATIVE, 0)],
                vec![read; 33],
            ] {
                assert!(matches!(
                    register_ops(&mut invalid, &registers),
                    Err(super::Error::Invariant(_))
                ));
            }
        }

        #[test]
        fn register_records_have_distinct_layout_and_operand_checks() {
            use super::{
                Architecture, Op, VM_R_JCC, VM_R_LOAD, VM_R_READ_REG, serialize_op, verify_record,
            };
            let mut op = Op::new(VM_R_READ_REG, 1);
            op.dst = 29;
            op.src = 3;
            op.flags = 3;
            let bytes = serialize_op(&op, Architecture::Register, 0, 0);
            assert_eq!(&bytes[..8], &[VM_R_READ_REG, 1, 29, 3, 255, 255, 1, 3]);
            assert!(verify_record(&bytes, Architecture::Register, 1).is_ok());
            assert!(verify_record(&bytes, Architecture::Stack, 1).is_err());
            for (at, value) in [(0, 0xa5), (1, 3), (2, 32), (3, 16), (3, 4), (7, 4), (16, 1)] {
                let mut invalid = bytes;
                invalid[at] = value;
                assert!(
                    verify_record(&invalid, Architecture::Register, 1).is_err(),
                    "{at}: {value}"
                );
            }
            let mut branch = Op::new(VM_R_JCC, 0);
            branch.flags = 15;
            for (target, valid) in [(-1, false), (0, true), (1, false)] {
                assert_eq!(
                    verify_record(
                        &serialize_op(&branch, Architecture::Register, 0, target),
                        Architecture::Register,
                        1
                    )
                    .is_ok(),
                    valid
                );
            }
            let mut load = Op::new(VM_R_LOAD, 8);
            load.base = 254;
            let good = serialize_op(&load, Architecture::Register, -17, 0);
            assert!(verify_record(&good, Architecture::Register, 1).is_ok());
            for (at, value) in [(4, 32), (5, 16), (5, 0), (6, 3), (7, 1)] {
                let mut bad = good;
                bad[at] = value;
                assert!(verify_record(&bad, Architecture::Register, 1).is_err());
            }
            let metadata = super::encode_metadata(0, 0, 1, 97, 16);
            assert_eq!(&metadata[16..24], &[97, 0, 0, 0, 0, 0, 0, 0]);
        }

        #[test]
        fn abi_bytes_have_fixed_layout() {
            let metadata =
                super::encode_metadata(-2, 0x04030201, 0x08070605, 0xa9, 0x100f0e0d0c0b0a09);
            assert_eq!(
                metadata,
                [
                    254, 255, 255, 255, 255, 255, 255, 255, 1, 2, 3, 4, 5, 6, 7, 8, 169, 0, 0, 0,
                    0, 0, 0, 0, 9, 10, 11, 12, 13, 14, 15, 16
                ]
            );
            let mut op = super::Op::new(3, 8);
            op.reg = 15;
            op.base = 254;
            op.index = 6;
            op.scale = 4;
            op.flags = 2;
            assert_eq!(
                super::serialize_op(&op, super::Architecture::Stack, -2, 0x0807060504030201),
                [
                    3, 8, 15, 254, 6, 4, 2, 0, 254, 255, 255, 255, 255, 255, 255, 255, 1, 2, 3, 4,
                    5, 6, 7, 8
                ]
            );
        }

        #[test]
        fn prefixes_and_machine_state_are_not_silently_lowered() {
            for bytes in [&[0xf0, 0x48, 0x83, 0x00, 0x01][..], &[0xf3, 0xa4][..]] {
                let i = instruction(bytes);
                assert!(lift(&i).unwrap().is_none());
                assert!(escape_ok(&i).is_ok());
            }
            for bytes in [&[0x67, 0x8b, 0x01][..], &[0x64, 0x48, 0x8b, 0x00][..]] {
                let i = instruction(bytes);
                assert!(lift(&i).is_err());
                assert!(escape_ok(&i).is_ok());
            }
            for bytes in [
                &[0x0f, 0x05][..],
                &[0xcd, 0x80][..],
                &[0xfa][..],
                &[0x0f, 0xae, 0x28][..],
            ] {
                assert!(escape_ok(&instruction(bytes)).is_err());
            }
        }

        #[test]
        fn lowering_retains_width_and_signed_immediates() {
            let ops = lift(&instruction(&[0xb8, 0xff, 0xff, 0xff, 0xff]))
                .unwrap()
                .unwrap();
            assert_eq!(ops[0].code, VM_PUSH_IMM);
            assert_eq!(ops[0].value, u32::MAX as i64);
            assert_eq!(ops[1].code, VM_POP_REG);
            assert_eq!((ops[1].reg, ops[1].width), (0, 4));
            let ops = lift(&instruction(&[0x48, 0x83, 0xc0, 0xff]))
                .unwrap()
                .unwrap();
            assert_eq!(ops[1].value, -1);
            assert_eq!(ops[2].width, 8);
            let ops = lift(&instruction(&[0x88, 0xe0])).unwrap().unwrap();
            assert_eq!((ops[0].reg, ops[0].width, ops[0].flags), (0, 1, 1));
        }

        #[test]
        fn frame_sizes_are_bounded_and_aligned() {
            assert_eq!(frame_depth(0).unwrap(), 0);
            assert_eq!(frame_depth(17).unwrap(), 32);
            assert_eq!(frame_depth(64 * 1024 * 1024).unwrap(), 64 * 1024 * 1024);
            assert!(frame_depth(64 * 1024 * 1024 + 1).is_err());
            assert!(frame_depth(u64::MAX).is_err());
        }

        #[test]
        fn final_return_uses_the_restored_native_stack() {
            let mut decoder = Decoder::with_ip(
                64,
                &RUNTIME[VM_RETURN_OFF..],
                VM_RETURN_OFF as u64,
                DecoderOptions::NONE,
            );
            assert_eq!(decoder.decode().mnemonic(), Mnemonic::Ret);
            let image = VmImage {
                code: RUNTIME.to_vec(),
                entries: BTreeMap::new(),
                moved: BTreeMap::new(),
                lengths: BTreeMap::new(),
                runtime: 0,
                islands: Vec::new(),
                island_frames: Vec::new(),
            };
            let regions = frame_regions(&image, &[]).unwrap();
            let region = regions
                .iter()
                .find(|region| region.va == VM_RETURN_OFF as u64)
                .unwrap();
            let rule = &region.rows[0].1;
            assert_eq!((rule.cfa_register, rule.cfa_offset), (7, 8));
            assert!(rule.cfa_expression.is_none());
            assert_eq!(
                rule.registers.get(&16),
                Some(&FrameRegisterRule::Offset(-8))
            );
            let tail = regions
                .iter()
                .find(|region| region.va == super::VM_TAIL_JUMP_OFF as u64)
                .unwrap();
            assert_eq!(tail.rows[0].1.cfa_register, 7);
            assert_eq!(tail.rows[0].1.cfa_offset, 8);
            assert_eq!(
                tail.rows[0].1.registers.get(&16),
                Some(&FrameRegisterRule::Offset(-8))
            );
        }
    }
}
