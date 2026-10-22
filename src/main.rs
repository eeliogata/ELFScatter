use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use gimli::{
    BaseAddresses, CfaRule, CieOrFde, DebugFrame, EhFrame, EhFrameOffset, LittleEndian,
    RegisterRule, UnwindContext, UnwindSection,
};
use iced_x86::{
    BlockEncoder, BlockEncoderOptions, ConditionCode, Decoder, DecoderOptions, FlowControl,
    Instruction, InstructionBlock, InstructionInfoFactory, Mnemonic, OpAccess, Register,
};
use lief::elf::{self, header, section, segment, symbol};
use lief::generic::{Binary as _, Relocation as _, Section as _, Symbol as _};

type Result<T> = std::result::Result<T, String>;

struct Options {
    inspect: bool,
    no_dispatch: bool,
    layout_fallback: bool,
    keep_metadata: bool,
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

#[derive(Clone, Copy, Eq, PartialEq)]
enum Scrub {
    Trap,
    Random,
    Off,
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
    patch: u64,
    patch_len: usize,
    blocks: Vec<Block>,
    unwind: Option<Vec<(u64, UnwindRule)>>,
}

#[derive(Clone, PartialEq, Eq)]
struct UnwindRule {
    cfa_register: u16,
    cfa_offset: i32,
    registers: BTreeMap<u16, FrameRegisterRule>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum FrameRegisterRule {
    Undefined,
    SameValue,
    Offset(i32),
    ValOffset(i32),
    Register(u16),
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
    mode: Mode,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Mode {
    Strong,
    Layout,
}

struct Skipped {
    address: u64,
    reason: String,
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("elfscatter: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<()> {
    let opts = parse_args()?;
    let binary = elf::Binary::parse(&opts.input).ok_or("cannot parse ELF")?;
    check_elf(&binary)?;
    let index = AnalysisIndex::new(&binary)?;
    let (candidates, automatic, mut skipped) = select_candidates(&binary, &index, &opts)?;
    let mut selected = Vec::new();
    for candidate in candidates {
        match analyze(&binary, &index, candidate.start, candidate.size) {
            Ok(function) => {
                let reason = strong_rejection(&function);
                let mode = if opts.no_dispatch || (opts.layout_fallback && reason.is_some()) {
                    Mode::Layout
                } else if let Some(reason) = reason {
                    if automatic {
                        skipped.push(Skipped {
                            address: candidate.start,
                            reason: reason.into(),
                        });
                        continue;
                    }
                    return Err(format!("0x{:x}: {reason}", candidate.start));
                } else {
                    Mode::Strong
                };
                selected.push(Selected {
                    candidate,
                    function,
                    mode,
                });
            }
            Err(err) if automatic => skipped.push(Skipped {
                address: candidate.start,
                reason: err,
            }),
            Err(err) => return Err(format!("0x{:x}: {err}", candidate.start)),
        }
    }
    if opts.inspect {
        if !automatic && selected.len() == 1 {
            let item = &selected[0];
            println!(
                "eligible 0x{:x}..0x{:x}  {} blocks  {}",
                item.function.start,
                item.function.end,
                item.function.blocks.len(),
                item.mode.name()
            );
            for block in &item.function.blocks {
                let len = block.len
                    + usize::from(item.mode == Mode::Strong && needs_endbr(&item.function, block))
                        * 4;
                println!("0x{:x}  {:3} bytes", block.old, len);
            }
        } else {
            for item in &selected {
                println!(
                    "0x{:x}  {:4} bytes  {:3} blocks  {}  {}",
                    item.function.start,
                    item.candidate.size,
                    item.function.blocks.len(),
                    item.mode.name(),
                    item.candidate
                        .names
                        .iter()
                        .next()
                        .map(String::as_str)
                        .unwrap_or("")
                );
            }
        }
        for item in &skipped {
            println!("0x{:x}  skipped  {}", item.address, item.reason);
        }
        println!("{} eligible, {} skipped", selected.len(), skipped.len());
        return Ok(());
    }
    if selected.is_empty() {
        return Err("no eligible functions".into());
    }
    let seed = match opts.seed {
        Some(seed) => seed,
        None => random_seed()?,
    };
    for item in &skipped {
        eprintln!("0x{:x}: skipped: {}", item.address, item.reason);
    }
    rewrite(binary, &index, &opts, &selected, seed, skipped.len())
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
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

fn parse_number(s: &str) -> Result<u64> {
    if let Some(hex) = s.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).map_err(|_| format!("invalid number: {s}"))
    } else {
        s.parse::<u64>().map_err(|_| format!("invalid number: {s}"))
    }
}

fn parse_args() -> Result<Options> {
    let mut args = env::args().skip(1);
    let command = args
        .next()
        .ok_or("usage: elfscatter <inspect|rewrite> INPUT [options]")?;
    let inspect = match command.as_str() {
        "inspect" => true,
        "rewrite" => false,
        _ => return Err("usage: elfscatter <inspect|rewrite> INPUT [options]".into()),
    };
    let input = PathBuf::from(args.next().ok_or("missing input ELF")?);
    let mut opts = Options {
        inspect,
        no_dispatch: false,
        layout_fallback: false,
        keep_metadata: false,
        scrub: Scrub::Trap,
        input,
        output: None,
        map: None,
        symbols: Vec::new(),
        exclude: BTreeSet::new(),
        address: None,
        size: None,
        seed: None,
    };
    while let Some(arg) = args.next() {
        if arg == "--no-dispatch" {
            opts.no_dispatch = true;
            continue;
        }
        if arg == "--layout-fallback" {
            opts.layout_fallback = true;
            continue;
        }
        if arg == "--keep-metadata" {
            opts.keep_metadata = true;
            continue;
        }
        if inspect && arg == "--scrub" {
            return Err("--scrub applies only to rewrite".into());
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
            "-o" | "--output" => opts.output = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown option: {arg}")),
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
    if opts.no_dispatch && opts.layout_fallback {
        return Err("--no-dispatch and --layout-fallback are mutually exclusive".into());
    }
    if inspect {
        if opts.output.is_some() || opts.seed.is_some() || opts.map.is_some() || opts.keep_metadata
        {
            return Err("inspect accepts only a function selector".into());
        }
    } else if opts.output.is_none() {
        return Err("rewrite requires -o OUTPUT".into());
    }
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
    Ok(opts)
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
            return Err(format!("unknown sized function: {name}"));
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
                ));
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

fn internal_edges(function: &Function) -> Vec<(u64, u8, u64)> {
    let mut edges = Vec::new();
    for block in &function.blocks {
        let targets = match block.exit {
            Exit::Branch {
                target,
                fallthrough,
                ..
            } => [Some(target), Some(fallthrough)],
            Exit::Jump(target) | Exit::Fallthrough(target) => [Some(target), None],
            Exit::Return => [None, None],
        };
        for (arm, target) in targets.into_iter().enumerate() {
            if let Some(target) = target
                && in_range(target, function.start, function.end)
            {
                edges.push((block.old, arm as u8, target));
            }
        }
    }
    edges
}

fn strong_rejection(function: &Function) -> Option<&'static str> {
    if internal_edges(function).is_empty() && !function.blocks.iter().any(|b| b.body.len() >= 4) {
        return Some("too short for fragment routing");
    }
    let mut info = InstructionInfoFactory::new();
    let mut decoder = Decoder::with_ip(64, &function.bytes, function.start, DecoderOptions::NONE);
    while decoder.can_decode() {
        let instr = decoder.decode();
        for used in info.info(&instr).used_registers() {
            let reg = used.register().full_register();
            if reg == Register::R10 || reg == Register::R11 {
                return Some("uses R10 or R11");
            }
        }
    }
    None
}

fn split_fragments(function: &Function, seed: u64) -> Vec<Block> {
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
                    34
                }
                Exit::Branch { .. } => 11,
                Exit::Jump(_) | Exit::Fallthrough(_) => 5,
                Exit::Return => 0,
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
                    34
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

struct AnalysisIndex {
    fdes: Vec<FrameRange>,
    functions: Vec<(u64, u64)>,
    relocation_sites: BTreeSet<u64>,
    relocation_targets: BTreeSet<u64>,
    references: BTreeMap<u64, Vec<u64>>,
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
        for rel in binary.relocations() {
            relocation_sites.insert(rel.address());
            let addend = rel.addend();
            if addend > 0 {
                relocation_targets.insert(addend as u64);
            }
            if let Some(sym) = rel.symbol() {
                let target = sym.value() as i128 + addend as i128;
                if let Ok(target) = u64::try_from(target) {
                    relocation_targets.insert(target);
                }
            }
        }
        let mut references: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
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
                    references.entry(target).or_default().push(instr.ip());
                }
                if instr.is_ip_rel_memory_operand() {
                    references
                        .entry(instr.ip_rel_memory_address())
                        .or_default()
                        .push(instr.ip());
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
            references,
        })
    }

    fn check(&self, start: u64, end: u64) -> Result<()> {
        for &(lo, hi) in &self.functions {
            if (lo > start && lo < end) || (lo < start && hi > start) {
                return Err(format!(
                    "function symbol overlaps selected range at 0x{lo:x}"
                ));
            }
        }
        if let Some(site) = self.relocation_sites.range(start..end).next() {
            return Err(format!("relocation inside selected function at 0x{site:x}"));
        }
        if let Some(target) = self.relocation_targets.range(start + 1..end).next() {
            return Err(format!(
                "relocation points into function interior at 0x{target:x}"
            ));
        }
        for (&target, sources) in self.references.range(start + 1..end) {
            if sources.iter().any(|&source| !in_range(source, start, end)) {
                return Err(format!(
                    "reference enters function interior at 0x{target:x}"
                ));
            }
        }
        Ok(())
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
    let bytes = binary.content_from_virtual_address(start, size);
    if bytes.len() != size as usize {
        return Err("cannot read complete function".into());
    }
    index.check(start, end)?;
    let unwind = index.unwind_for(binary, start, end)?;

    let mut decoder = Decoder::with_ip(64, bytes, start, DecoderOptions::NONE);
    let mut instructions = Vec::new();
    let mut boundaries = BTreeSet::from([start]);
    let mut ips = BTreeSet::new();
    while decoder.can_decode() {
        let instr = decoder.decode();
        if instr.is_invalid() {
            return Err(format!("invalid instruction at 0x{:x}", instr.ip()));
        }
        ips.insert(instr.ip());
        if instr.is_ip_rel_memory_operand() && in_range(instr.ip_rel_memory_address(), start, end) {
            return Err(format!(
                "RIP-relative reference into selected function at 0x{:x}",
                instr.ip()
            ));
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
            FlowControl::Return if instr.mnemonic() == Mnemonic::Ret => {
                if instr.next_ip() < end {
                    boundaries.insert(instr.next_ip());
                }
            }
            _ => {
                return Err(format!(
                    "unsupported control transfer at 0x{:x}",
                    instr.ip()
                ));
            }
        }
        instructions.push(instr);
    }
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
            return Err(format!("empty block at 0x{old:x}"));
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
            FlowControl::Return => Exit::Return,
            _ => {
                if stop == end {
                    return Err("function ends with implicit fallthrough".into());
                }
                Exit::Fallthrough(stop)
            }
        };
        let tail = match exit {
            Exit::Branch { .. } => 11,
            Exit::Jump(_) | Exit::Fallthrough(_) => 5,
            Exit::Return => 0,
        };
        let len = body.iter().map(|x| x.len()).sum::<usize>() + tail;
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
        };
        for target in targets {
            if in_range(target, start, end) && !block_ips.contains(&target) {
                return Err(format!("edge enters middle of block at 0x{target:x}"));
            }
        }
    }

    let patch = if bytes.starts_with(&[0xf3, 0x0f, 0x1e, 0xfa]) {
        start + 4
    } else {
        start
    };
    let mut patch_len = 0;
    for instr in &instructions {
        if instr.ip() < patch {
            continue;
        }
        patch_len += instr.len();
        if patch_len >= 5 {
            break;
        }
    }
    if patch_len < 5 || patch + patch_len as u64 > end {
        return Err("entry has insufficient instruction bytes for a direct jump".into());
    }
    for block in &blocks {
        if block.old > patch && block.old < patch + patch_len as u64 {
            return Err("entry patch would overwrite an internal branch target".into());
        }
    }
    Ok(Function {
        start,
        end,
        bytes: bytes.to_vec(),
        patch,
        patch_len,
        blocks,
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
            .ok_or_else(|| format!("unmapped branch target 0x{target:x}"))
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

fn encoded_capacity(function: &Function) -> Result<usize> {
    Ok(function.blocks.iter().try_fold(0usize, |sum, block| {
        sum.checked_add(block.len).ok_or("clone length overflow")
    })?)
}

fn entry_offset(function: &Function, seed: u64) -> Result<usize> {
    let mut offset = 0usize;
    for index in permute_all(function.blocks.len(), seed) {
        let block = &function.blocks[index];
        if block.old == function.start {
            return Ok(offset);
        }
        offset = offset
            .checked_add(block.len)
            .ok_or("clone length overflow")?;
    }
    Err("entry block missing".into())
}

fn write_body(
    function: &Function,
    block: &Block,
    base: u64,
    code: &mut Vec<u8>,
    moved: &BTreeMap<u64, u64>,
    entries: &BTreeMap<u64, u64>,
    state: Option<u64>,
) -> Result<()> {
    for instr in &block.body {
        let address = base + code.len() as u64;
        if instr.is_ip_rel_memory_operand()
            || (instr.flow_control() == FlowControl::Call && instr.is_call_near())
        {
            let mut relocated = *instr;
            if instr.flow_control() == FlowControl::Call && instr.is_call_near() {
                let target = instr.near_branch_target();
                relocated.set_near_branch64(match entries.get(&target) {
                    Some(&entry) => entry,
                    None => destination(target, function, moved, entries)?,
                });
            }
            let encoded = BlockEncoder::encode(
                64,
                InstructionBlock::new(std::slice::from_ref(&relocated), address),
                BlockEncoderOptions::NONE,
            )
            .map_err(|e| format!("cannot relocate instruction 0x{:x}: {e}", instr.ip()))?;
            if encoded.code_buffer.len() != instr.len() {
                return Err(format!("instruction 0x{:x} changed width", instr.ip()));
            }
            code.extend_from_slice(&encoded.code_buffer);
        } else {
            let offset = (instr.ip() - function.start) as usize;
            code.extend_from_slice(&function.bytes[offset..offset + instr.len()]);
        }
        if matches!(
            instr.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) && let Some(state) = state
        {
            let address = base + code.len() as u64;
            code.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
            code.extend_from_slice(&rel32(address + 7, state)?);
        }
    }
    Ok(())
}

fn write_exit<F>(block: &Block, tail: u64, code: &mut Vec<u8>, mut route: F) -> Result<()>
where
    F: FnMut(u64, u8) -> Result<u64>,
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
        Exit::Return => {}
    }
    Ok(())
}

fn encode_direct(
    function: &Function,
    base: u64,
    seed: u64,
    entries: &BTreeMap<u64, u64>,
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
        write_body(function, block, base, &mut code, &moved, entries, None)?;
        let tail = base + code.len() as u64;
        write_exit(block, tail, &mut code, |target, _| {
            destination(target, function, &moved, entries)
        })?;
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

const ROUTE_STUB_LEN: usize = 26;
const RECORD_LEN: usize = 24;

struct StrongFragment {
    function: usize,
    block: Block,
    va: u64,
}

struct RoutePath {
    records: Vec<u64>,
    handlers: Vec<usize>,
}

struct StrongRoute {
    function: usize,
    source: u64,
    arm: u8,
    target: u64,
    path: RoutePath,
    paired: bool,
    va: u64,
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
    Entry(usize),
    Stub(usize),
    Record(usize, usize),
    Handler(usize),
    Layout(usize),
}

struct StrongLayout {
    fragments: Vec<StrongFragment>,
    routes: Vec<StrongRoute>,
    handlers: Vec<Handler>,
    entries: Vec<u64>,
    layouts: Vec<u64>,
    parts: Vec<Part>,
    order: Vec<usize>,
    capacity: usize,
    base: u64,
}

fn next_random(state: &mut u64) -> u64 {
    *state ^= *state >> 12;
    *state ^= *state << 25;
    *state ^= *state >> 27;
    state.wrapping_mul(0x2545f4914f6cdd1d)
}

fn route_state(base: u64, seed: u64, old: u64) -> u64 {
    base + function_seed(seed ^ 0x7f4a7c159e3779b9, old) % 4096
}

fn route_input(route: &StrongRoute, seed: u64) -> (u8, bool) {
    let mut state = function_seed(
        seed ^ 0xd1310ba698dfb5ac,
        route.source ^ route.target.rotate_left(17) ^ route.arm as u64,
    );
    let registers = [0, 1, 2, 6, 7];
    let register = registers[next_random(&mut state) as usize % registers.len()];
    (register, next_random(&mut state) & 1 != 0)
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
        code.extend_from_slice(&[0x4f, 0x8d, 0x14, 0x1a, 0x4d, 0x87, 0xda]);
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

fn check_route_code(code: &[u8]) -> Result<()> {
    let mut decoder = Decoder::with_ip(64, code, 0, DecoderOptions::NONE);
    let mut info = InstructionInfoFactory::new();
    let mut ended = false;
    while decoder.can_decode() {
        let instruction = decoder.decode();
        if instruction.is_invalid() || instruction.rflags_modified() != 0 || ended {
            return Err("invalid route code".into());
        }
        match instruction.flow_control() {
            FlowControl::Next => {
                for used in info.info(&instruction).used_registers() {
                    if matches!(
                        used.access(),
                        OpAccess::Write
                            | OpAccess::CondWrite
                            | OpAccess::ReadWrite
                            | OpAccess::ReadCondWrite
                    ) && !matches!(
                        used.register().full_register(),
                        Register::R10 | Register::R11
                    ) {
                        return Err("route code writes a source register".into());
                    }
                }
            }
            FlowControl::UnconditionalBranch if !decoder.can_decode() => ended = true,
            _ => return Err("invalid route transfer".into()),
        }
    }
    if !ended {
        return Err("route code has no exit".into());
    }
    Ok(())
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
    fn new(selected: &[Selected], seed: u64) -> Result<Self> {
        let mut fragments = Vec::new();
        let mut routes = Vec::new();
        let mut handlers = Vec::new();
        for (index, item) in selected.iter().enumerate() {
            if item.mode != Mode::Strong {
                continue;
            }
            for block in split_fragments(&item.function, seed) {
                fragments.push(StrongFragment {
                    function: index,
                    block,
                    va: 0,
                });
            }
        }
        for fragment in &fragments {
            let function = &selected[fragment.function].function;
            let paired = matches!(fragment.block.exit,
                Exit::Branch { target, fallthrough, .. }
                    if in_range(target, function.start, function.end)
                        && in_range(fallthrough, function.start, function.end));
            let mut shared_state = function_seed(seed ^ 0x3c6ef372fe94f82b, fragment.block.old);
            let shared = if paired {
                Some(add_handler(&mut handlers, &mut shared_state, false)?)
            } else {
                None
            };
            let decoy = if let Exit::Branch {
                target,
                fallthrough,
                ..
            } = fragment.block.exit
                && paired
            {
                let candidates: Vec<_> = fragments
                    .iter()
                    .filter(|other| {
                        other.function == fragment.function
                            && other.block.old != target
                            && other.block.old != fallthrough
                    })
                    .map(|other| other.block.old)
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
            let targets = match fragment.block.exit {
                Exit::Branch {
                    target,
                    fallthrough,
                    ..
                } => [Some(target), Some(fallthrough), decoy],
                Exit::Jump(target) | Exit::Fallthrough(target) => [Some(target), None, None],
                Exit::Return => [None, None, None],
            };
            for (arm, target) in targets.into_iter().enumerate() {
                let Some(target) = target else { continue };
                if !in_range(target, function.start, function.end) {
                    continue;
                }
                let mut state = function_seed(
                    seed ^ fragment.block.old.rotate_left(13),
                    target ^ (arm as u64),
                );
                let count = if arm == 2 {
                    2
                } else {
                    2 + (next_random(&mut state) % 3) as usize
                };
                let mut path_handlers = Vec::new();
                for step in 0..count {
                    path_handlers.push(
                        if step == 0
                            && let Some(id) = shared
                        {
                            id
                        } else {
                            add_handler(&mut handlers, &mut state, step + 1 == count)?
                        },
                    );
                }
                routes.push(StrongRoute {
                    function: fragment.function,
                    source: fragment.block.old,
                    arm: arm as u8,
                    target,
                    path: RoutePath {
                        records: vec![0; count],
                        handlers: path_handlers,
                    },
                    paired,
                    va: 0,
                });
            }
        }
        let mut parts = Vec::new();
        for index in 0..fragments.len() {
            parts.push(Part::Fragment(index));
        }
        for (index, item) in selected.iter().enumerate() {
            if item.mode == Mode::Strong {
                parts.push(Part::Entry(index));
            }
        }
        for (index, route) in routes.iter().enumerate() {
            if !route.paired {
                parts.push(Part::Stub(index));
            }
            for step in 0..route.path.records.len() {
                parts.push(Part::Record(index, step));
            }
        }
        for index in 0..handlers.len() {
            parts.push(Part::Handler(index));
        }
        for (index, item) in selected.iter().enumerate() {
            if item.mode == Mode::Layout {
                parts.push(Part::Layout(index));
            }
        }
        let order = permute_all(parts.len(), seed ^ 0x243f6a8885a308d3);
        let mut layout = Self {
            fragments,
            routes,
            handlers,
            entries: vec![0; selected.len()],
            layouts: vec![0; selected.len()],
            order,
            parts,
            capacity: 0,
            base: 0,
        };
        for part in &layout.parts {
            layout.capacity = layout
                .capacity
                .checked_add(layout.part_len(*part, selected)?)
                .ok_or("clone length overflow")?;
        }
        Ok(layout)
    }

    fn part_len(&self, part: Part, selected: &[Selected]) -> Result<usize> {
        Ok(match part {
            Part::Fragment(index) => {
                let item = &self.fragments[index];
                item.block.len
                    + usize::from(needs_endbr(&selected[item.function].function, &item.block)) * 4
            }
            Part::Entry(_) => 16,
            Part::Stub(_) => ROUTE_STUB_LEN,
            Part::Record(_, _) => RECORD_LEN,
            Part::Handler(index) => self.handlers[index].code.len(),
            Part::Layout(index) => encoded_capacity(&selected[index].function)?,
        })
    }

    fn place(&mut self, base: u64, selected: &[Selected]) -> Result<()> {
        self.base = base;
        let mut cursor = base;
        for &part_index in &self.order {
            let part = self.parts[part_index];
            match part {
                Part::Fragment(index) => self.fragments[index].va = cursor,
                Part::Entry(index) => self.entries[index] = cursor,
                Part::Stub(index) => self.routes[index].va = cursor,
                Part::Record(index, step) => self.routes[index].path.records[step] = cursor,
                Part::Handler(index) => self.handlers[index].va = cursor,
                Part::Layout(index) => self.layouts[index] = cursor,
            }
            cursor = cursor
                .checked_add(self.part_len(part, selected)? as u64)
                .ok_or("clone address overflow")?;
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

fn route_stub(route: &StrongRoute, handlers: &[Handler], base: u64, seed: u64) -> Result<Vec<u8>> {
    let mut code = Vec::with_capacity(ROUTE_STUB_LEN);
    let state = route_state(base, seed, route.source);
    let first = route.path.records[0];
    let handler = handlers[route.path.handlers[0]].va;
    let (register, variant) = route_input(route, seed);
    if variant {
        code.extend_from_slice(&[0x4c, 0x8b, 0xd0 | register]);
        code.extend_from_slice(&[0x49, 0xf7, 0xd2]);
        code.extend_from_slice(&[0x4f, 0x8d, 0x1c, 0x13]);
        code.extend_from_slice(&[0x49, 0xf7, 0xd2]);
    } else {
        code.extend_from_slice(&[0x4d, 0x8d, 0x1c, 0x03 | (register << 3)]);
        code.extend_from_slice(&[0x4c, 0x8b, 0xd0 | register]);
        code.extend_from_slice(&[0x49, 0xf7, 0xd2]);
    }
    code.extend_from_slice(&[0x4f, 0x8d, 0x94, 0x13]);
    code.extend_from_slice(&rel32(state - 1, first)?);
    if !variant {
        code.extend_from_slice(&[0x90; 3]);
    }
    code.push(0xe9);
    code.extend_from_slice(&rel32(route.va + ROUTE_STUB_LEN as u64, handler)?);
    check_route_code(&code)?;
    Ok(code)
}

fn route_record(
    route: &StrongRoute,
    step: usize,
    handlers: &[Handler],
    moved: &BTreeMap<u64, u64>,
    base: u64,
    seed: u64,
) -> Result<[u8; RECORD_LEN]> {
    let path = &route.path;
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
        !route_state(base, seed, route.target).wrapping_sub(next)
    } else {
        function_seed(seed ^ 0x9e3779b97f4a7c15, va)
    };
    bytes[16..24].copy_from_slice(&third.to_le_bytes());
    Ok(bytes)
}

impl StrongLayout {
    fn encode(&self, selected: &[Selected], seed: u64) -> Result<CodeImage> {
        let mut moved = BTreeMap::new();
        let mut lengths = BTreeMap::new();
        for fragment in &self.fragments {
            moved.insert(fragment.block.old, fragment.va);
            lengths.insert(
                fragment.block.old,
                fragment.block.len
                    + usize::from(needs_endbr(
                        &selected[fragment.function].function,
                        &fragment.block,
                    )) * 4,
            );
        }
        let mut entries = BTreeMap::new();
        for (index, item) in selected.iter().enumerate() {
            let va = if item.mode == Mode::Strong {
                self.entries[index]
            } else {
                self.layouts[index]
                    .checked_add(entry_offset(
                        &item.function,
                        function_seed(seed, item.function.start),
                    )? as u64)
                    .ok_or("clone address overflow")?
            };
            entries.insert(item.function.start, va);
        }
        let route_addresses: BTreeMap<_, _> = self
            .routes
            .iter()
            .map(|route| ((route.function, route.source, route.arm), route.va))
            .collect();
        let mut code = vec![0xcc; self.capacity];
        for part in &self.parts {
            match *part {
                Part::Fragment(index) => {
                    let fragment = &self.fragments[index];
                    let function = &selected[fragment.function].function;
                    let mut bytes = Vec::with_capacity(lengths[&fragment.block.old]);
                    if needs_endbr(function, &fragment.block) {
                        bytes.extend_from_slice(&ENDBR64);
                    }
                    write_body(
                        function,
                        &fragment.block,
                        fragment.va,
                        &mut bytes,
                        &moved,
                        &entries,
                        Some(route_state(self.base, seed, fragment.block.old)),
                    )?;
                    let tail = fragment.va + bytes.len() as u64;
                    if let Exit::Branch {
                        target,
                        fallthrough,
                        cc,
                    } = fragment.block.exit
                        && in_range(target, function.start, function.end)
                        && in_range(fallthrough, function.start, function.end)
                    {
                        let true_route = self
                            .routes
                            .iter()
                            .find(|route| {
                                route.function == fragment.function
                                    && route.source == fragment.block.old
                                    && route.arm == 0
                            })
                            .ok_or("missing true route")?;
                        let false_route = self
                            .routes
                            .iter()
                            .find(|route| {
                                route.function == fragment.function
                                    && route.source == fragment.block.old
                                    && route.arm == 1
                            })
                            .ok_or("missing false route")?;
                        let decoy_route = self
                            .routes
                            .iter()
                            .find(|route| {
                                route.function == fragment.function
                                    && route.source == fragment.block.old
                                    && route.arm == 2
                            })
                            .unwrap_or(false_route);
                        if true_route.path.handlers[0] != false_route.path.handlers[0] {
                            return Err("branch routes have different handlers".into());
                        }
                        if true_route.path.handlers[0] != decoy_route.path.handlers[0] {
                            return Err("decoy route has a different handler".into());
                        }
                        let state = route_state(self.base, seed, fragment.block.old);
                        bytes.extend_from_slice(&[0x4d, 0x8d, 0x93]);
                        bytes.extend_from_slice(&rel32(state, decoy_route.path.records[0])?);
                        bytes.extend_from_slice(&[0x4d, 0x8d, 0x9b]);
                        bytes.extend_from_slice(&rel32(state, true_route.path.records[0])?);
                        let condition = condition_opcode(cc)?;
                        bytes.extend_from_slice(&[0x4d, 0x0f, condition - 0x40, 0xd3]);
                        bytes.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
                        bytes.extend_from_slice(&rel32(tail + 25, false_route.path.records[0])?);
                        bytes.extend_from_slice(&[0x4d, 0x0f, (condition ^ 1) - 0x40, 0xd3]);
                        bytes.push(0xe9);
                        let handler = self.handlers[true_route.path.handlers[0]].va;
                        bytes.extend_from_slice(&rel32(tail + 34, handler)?);
                        check_route_code(&bytes[(tail - fragment.va) as usize..])?;
                    } else {
                        write_exit(&fragment.block, tail, &mut bytes, |target, arm| {
                            if in_range(target, function.start, function.end) {
                                route_addresses
                                    .get(&(fragment.function, fragment.block.old, arm))
                                    .copied()
                                    .ok_or_else(|| {
                                        format!("missing route at 0x{:x}", fragment.block.old)
                                    })
                            } else {
                                Ok(entries.get(&target).copied().unwrap_or(target))
                            }
                        })?;
                    }
                    put(
                        &mut code,
                        self.base,
                        fragment.va,
                        &bytes,
                        lengths[&fragment.block.old],
                    )?;
                }
                Part::Entry(index) => {
                    let entry = self.entries[index];
                    let start = selected[index].function.start;
                    let target = *moved.get(&start).ok_or("entry fragment missing")?;
                    let mut bytes = ENDBR64.to_vec();
                    bytes.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
                    bytes.extend_from_slice(&rel32(
                        entry + 11,
                        route_state(self.base, seed, start),
                    )?);
                    bytes.push(0xe9);
                    bytes.extend_from_slice(&rel32(entry + 16, target)?);
                    put(&mut code, self.base, entry, &bytes, 16)?;
                }
                Part::Stub(index) => {
                    let route = &self.routes[index];
                    put(
                        &mut code,
                        self.base,
                        route.va,
                        &route_stub(route, &self.handlers, self.base, seed)?,
                        ROUTE_STUB_LEN,
                    )?;
                }
                Part::Record(index, step) => {
                    let route = &self.routes[index];
                    let va = route.path.records[step];
                    let bytes = route_record(route, step, &self.handlers, &moved, self.base, seed)?;
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
        moved: &BTreeMap<u64, u64>,
        seed: u64,
    ) -> Result<()> {
        for handler in &self.handlers {
            if result.content_from_virtual_address(handler.va, 4) != ENDBR64 {
                return Err("rewritten ELF has an invalid handler".into());
            }
        }
        for route in &self.routes {
            let target = moved[&route.target];
            if result.content_from_virtual_address(target, 4) != ENDBR64 {
                return Err("rewritten ELF has an invalid indirect target".into());
            }
            let path = &route.path;
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
                    return Err("rewritten ELF has an invalid route".into());
                }
                if step + 1 == path.records.len() {
                    let state = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
                    if (!state).wrapping_add(target) != route_state(self.base, seed, route.target) {
                        return Err("rewritten ELF has an invalid route state".into());
                    }
                }
                if step > 0 {
                    let second = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
                    let previous = &self.handlers[path.handlers[step - 1]];
                    if previous.decode(va, second, previous.key2) != handler.va {
                        return Err("rewritten ELF has an invalid handler link".into());
                    }
                }
            }
        }
        Ok(())
    }
}

fn temporary_path(output: &Path) -> Result<PathBuf> {
    let dir = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let name = output
        .file_name()
        .ok_or("invalid output path")?
        .to_string_lossy();
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    Ok(dir.join(format!(
        ".{name}.elfscatter.{}.{}",
        std::process::id(),
        nonce
    )))
}

struct Temp(PathBuf);

impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
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
        .ok_or_else(|| format!("missing unwind row at 0x{address:x}"))
}

fn frame_region(
    function: &Function,
    block: &Block,
    va: u64,
    len: usize,
    strong: bool,
) -> Result<FrameRegion> {
    let source = function.unwind.as_ref().ok_or("missing unwind rows")?;
    let prefix = usize::from(strong && needs_endbr(function, block)) * 4;
    let mut boundaries = BTreeMap::new();
    let mut cursor = prefix;
    boundaries.insert(block.old, cursor);
    for instruction in &block.body {
        boundaries.entry(instruction.ip()).or_insert(cursor);
        cursor += instruction.len();
        boundaries.entry(instruction.next_ip()).or_insert(cursor);
        if strong
            && matches!(
                instruction.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            )
        {
            cursor += 7;
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
    for (index, item) in selected.iter().enumerate() {
        let Some(rows) = item.function.unwind.as_ref() else {
            continue;
        };
        if item.mode == Mode::Strong {
            let mut handler_seen = BTreeSet::new();
            regions.push(FrameRegion {
                va: layout.entries[index],
                len: 16,
                rows: vec![(0, unwind_rule(rows, item.function.start)?)],
            });
            for fragment in layout
                .fragments
                .iter()
                .filter(|fragment| fragment.function == index)
            {
                regions.push(frame_region(
                    &item.function,
                    &fragment.block,
                    fragment.va,
                    image.lengths[&fragment.block.old],
                    true,
                )?);
            }
            for route in layout.routes.iter().filter(|route| route.function == index) {
                let fragment = layout
                    .fragments
                    .iter()
                    .find(|fragment| {
                        fragment.function == index && fragment.block.old == route.source
                    })
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
                        len: ROUTE_STUB_LEN as u32,
                        rows: vec![(0, rule.clone())],
                    });
                }
                for &handler_index in &route.path.handlers {
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
        } else {
            for block in &item.function.blocks {
                regions.push(frame_region(
                    &item.function,
                    block,
                    image.moved[&block.old],
                    image.lengths[&block.old],
                    false,
                )?);
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
        old.cfa_register != rule.cfa_register || old.cfa_offset != rule.cfa_offset
    }) {
        if rule.cfa_offset >= 0 {
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
    for (&register, &value) in &rule.registers {
        if previous.and_then(|old| old.registers.get(&register)) == Some(&value) {
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
                let factor = -(offset as i64);
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
                let factor = -(offset as i64);
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
                uleb(other.into(), out);
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

fn debug_frame_payload(regions: &[FrameRegion]) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    let cie = out.len();
    out.extend_from_slice(&[0; 4]);
    out.extend_from_slice(&u32::MAX.to_le_bytes());
    out.extend_from_slice(&[1, 0, 1, 0x7f, 16]);
    finish_cfi_record(&mut out, cie, 8)?;
    for region in regions {
        let start = out.len();
        out.extend_from_slice(&[0; 8]);
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

fn unwind_capacity(
    index: &AnalysisIndex,
    layout: &StrongLayout,
    selected: &[Selected],
) -> Result<usize> {
    let mut count = 0usize;
    let mut rows = 0usize;
    for (index, item) in selected.iter().enumerate() {
        let Some(unwind) = item.function.unwind.as_ref() else {
            continue;
        };
        let regions = if item.mode == Mode::Strong {
            1 + layout
                .fragments
                .iter()
                .filter(|fragment| fragment.function == index)
                .count()
                + layout
                    .routes
                    .iter()
                    .filter(|route| route.function == index)
                    .map(|route| usize::from(!route.paired) + route.path.handlers.len())
                    .sum::<usize>()
        } else {
            item.function.blocks.len()
        };
        count += regions;
        rows += unwind.len() + regions;
    }
    let value = 4096usize
        .checked_add(
            index
                .fdes
                .len()
                .checked_mul(8)
                .ok_or("unwind size overflow")?,
        )
        .and_then(|n| n.checked_add(count.checked_mul(128)?))
        .and_then(|n| n.checked_add(rows.checked_mul(256)?))
        .ok_or("unwind size overflow")?;
    if value > 128 * 1024 * 1024 {
        return Err("unwind metadata exceeds size limit".into());
    }
    Ok(value)
}

fn patch_unwind_header(
    path: &Path,
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
    let mut bytes = fs::read(path).map_err(|e| e.to_string())?;
    if bytes.len() < 64 {
        return Err("invalid ELF header".into());
    }
    let read16 =
        |offset: usize| u16::from_le_bytes(bytes[offset..offset + 2].try_into().unwrap()) as usize;
    let read64 = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    let phoff = usize::try_from(read64(32)).map_err(|_| "program header offset out of range")?;
    let shoff = usize::try_from(read64(40)).map_err(|_| "section header offset out of range")?;
    let phentsize = read16(54);
    let phnum = read16(56);
    let shentsize = read16(58);
    let shnum = read16(60);
    if phentsize != 56 || shentsize != 64 || section_index >= shnum {
        return Err("unsupported ELF header table shape".into());
    }
    let mut phdr = None;
    for i in 0..phnum {
        let offset = phoff
            .checked_add(i * phentsize)
            .ok_or("program header overflow")?;
        if offset + phentsize > bytes.len() {
            return Err("truncated program header".into());
        }
        if u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) == 0x6474e550 {
            phdr = Some(offset);
            break;
        }
    }
    let phdr = phdr.ok_or("missing PT_GNU_EH_FRAME")?;
    let shdr = shoff
        .checked_add(section_index * shentsize)
        .ok_or("section header overflow")?;
    if shdr + shentsize > bytes.len() {
        return Err("truncated section header".into());
    }
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
    fs::write(path, bytes).map_err(|e| e.to_string())
}

fn append_aligned(bytes: &mut Vec<u8>, content: &[u8]) -> Result<u64> {
    while bytes.len() & 7 != 0 {
        bytes.push(0);
    }
    let offset = u64::try_from(bytes.len()).map_err(|_| "ELF file offset out of range")?;
    bytes.extend_from_slice(content);
    Ok(offset)
}

fn append_debug_frame(path: &Path, content: &[u8]) -> Result<u64> {
    let mut bytes = fs::read(path).map_err(|e| e.to_string())?;
    if bytes.len() < 64 || &bytes[..4] != b"\x7fELF" || bytes[4] != 2 || bytes[5] != 1 {
        return Err("unsupported ELF header".into());
    }
    let read16 = |offset: usize| u16::from_le_bytes(bytes[offset..offset + 2].try_into().unwrap());
    let read64 = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    let shoff = usize::try_from(read64(40)).map_err(|_| "section table offset out of range")?;
    let shentsize = read16(58) as usize;
    let shnum = read16(60) as usize;
    let shstrndx = read16(62) as usize;
    if shentsize != 64 || shnum == 0 || shnum >= 0xff00 || shstrndx >= shnum {
        return Err("unsupported ELF section table".into());
    }
    let end = shoff
        .checked_add(
            shnum
                .checked_mul(shentsize)
                .ok_or("section table overflow")?,
        )
        .ok_or("section table overflow")?;
    if end > bytes.len() {
        return Err("truncated ELF section table".into());
    }
    let mut table = bytes[shoff..end].to_vec();
    let shstr = shstrndx * shentsize;
    if u32::from_le_bytes(table[shstr + 4..shstr + 8].try_into().unwrap()) != 3 {
        return Err("invalid section-name table".into());
    }
    let names_offset = usize::try_from(u64::from_le_bytes(
        table[shstr + 24..shstr + 32].try_into().unwrap(),
    ))
    .map_err(|_| "section-name table offset out of range")?;
    let names_size = usize::try_from(u64::from_le_bytes(
        table[shstr + 32..shstr + 40].try_into().unwrap(),
    ))
    .map_err(|_| "section-name table size out of range")?;
    let names_end = names_offset
        .checked_add(names_size)
        .ok_or("section-name table overflow")?;
    if names_size == 0 || names_end > bytes.len() || bytes[names_end - 1] != 0 {
        return Err("invalid section-name table".into());
    }
    let name = u32::try_from(names_size).map_err(|_| "section-name table too large")?;
    let mut names = bytes[names_offset..names_end].to_vec();
    names.extend_from_slice(b".debug_frame\0");
    let new_names_offset = append_aligned(&mut bytes, &names)?;
    let section_offset = append_aligned(&mut bytes, content)?;
    table[shstr + 24..shstr + 32].copy_from_slice(&new_names_offset.to_le_bytes());
    table[shstr + 32..shstr + 40].copy_from_slice(&(names.len() as u64).to_le_bytes());
    let mut section = [0u8; 64];
    section[..4].copy_from_slice(&name.to_le_bytes());
    section[4..8].copy_from_slice(&1u32.to_le_bytes());
    section[8..16].copy_from_slice(&section::Flags::COMPRESSED.bits().to_le_bytes());
    section[24..32].copy_from_slice(&section_offset.to_le_bytes());
    section[32..40].copy_from_slice(&(content.len() as u64).to_le_bytes());
    section[48..56].copy_from_slice(&8u64.to_le_bytes());
    table.extend_from_slice(&section);
    let new_shoff = append_aligned(&mut bytes, &table)?;
    bytes[40..48].copy_from_slice(&new_shoff.to_le_bytes());
    bytes[60..62].copy_from_slice(&((shnum + 1) as u16).to_le_bytes());
    fs::write(path, bytes).map_err(|e| e.to_string())?;
    Ok(section_offset)
}

struct Rewrite {
    patch_va: u64,
    patch: Vec<u8>,
    retired_va: u64,
    retired: Vec<u8>,
}

fn rewrite(
    binary: elf::Binary,
    index: &AnalysisIndex,
    opts: &Options,
    selected: &[Selected],
    seed: u64,
    skipped: usize,
) -> Result<()> {
    let input = &opts.input;
    let output = opts.output.as_ref().unwrap();
    let map = opts.map.as_deref();
    let scrub = opts.scrub;
    let old_loads: Vec<u64> = binary
        .segments()
        .filter(|s| s.p_type() == segment::Type::LOAD)
        .map(|s| s.virtual_address())
        .collect();
    let old_interpreter = binary.interpreter();
    let old_entrypoint = binary.header().entrypoint();
    let mut old_dynamic: Vec<_> = binary
        .dynamic_symbols()
        .map(|s| (s.name(), s.value(), s.size()))
        .collect();
    old_dynamic.sort();
    let has_unwind = selected.iter().any(|item| item.function.unwind.is_some());
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
    let mut layout = StrongLayout::new(selected, seed)?;
    let extra = if has_unwind {
        unwind_capacity(index, &layout, selected)?
    } else {
        0
    };
    let trailer_pad = if has_unwind {
        (4 - layout.capacity % 4) % 4
    } else {
        0
    };
    let mut size = layout
        .capacity
        .checked_add(trailer_pad)
        .and_then(|n| n.checked_add(extra))
        .ok_or("clone length overflow")?;
    let mut first = Some(binary);
    let mut prepared = None;
    for _ in 0..3 {
        let mut candidate = if let Some(original) = first.take() {
            original
        } else {
            elf::Binary::parse(input).ok_or("cannot reparse input ELF")?
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
        layout.place(base, selected)?;
        let mut image = layout.encode(selected, seed)?;
        let unwind_header = if has_unwind {
            let regions = frame_regions(&layout, selected, &image)?;
            image.code.resize(layout.capacity + trailer_pad, 0xcc);
            let (payload, offset, len) = unwind_payload(
                index,
                &regions,
                base + layout.capacity as u64 + trailer_pad as u64,
                old_eh_va.unwrap(),
            )?;
            if payload.len() > extra {
                return Err("unwind metadata exceeded reserved space".into());
            }
            image.code.extend_from_slice(&payload);
            Some((
                base + layout.capacity as u64 + trailer_pad as u64 + offset as u64,
                len,
                regions.len(),
            ))
        } else {
            None
        };
        if image.code.len() == size {
            prepared = Some((candidate, base, image, unwind_header));
            break;
        }
        size = image.code.len();
    }
    let (mut binary, base, image, unwind_header) =
        prepared.ok_or("added segment size did not converge")?;
    let debug_frame = if has_unwind {
        let regions = frame_regions(&layout, selected, &image)?;
        let plain = debug_frame_payload(&regions)?;
        let compressed = compressed_debug_frame(&plain)?;
        Some((regions, plain, compressed))
    } else {
        None
    };
    let mut rewritten = Vec::with_capacity(selected.len());
    for item in selected {
        let function = &item.function;
        let mut patch = vec![0xe9];
        patch.extend_from_slice(&rel32(function.patch + 5, image.entries[&function.start])?);
        if scrub == Scrub::Off {
            patch.resize(function.patch_len, 0x90);
        }
        let retired_va = function.patch + 5;
        let retired = scrub_bytes(
            scrub,
            (function.end - retired_va) as usize,
            function_seed(seed, function.start),
        );
        rewritten.push(Rewrite {
            patch_va: function.patch,
            patch,
            retired_va,
            retired,
        });
    }
    binary.patch_address(base, &image.code);
    for item in &rewritten {
        binary.patch_address(item.patch_va, &item.patch);
        if !item.retired.is_empty() {
            binary.patch_address(item.retired_va, &item.retired);
        }
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
        for name in removable {
            if let Some(section) = binary.section_by_name(&name) {
                let section: elf::Section<'static> = unsafe { std::mem::transmute(section) };
                binary.remove_section(&section, true);
            }
        }
        refresh_build_id(&mut binary, seed)?
    } else {
        None
    };

    let tmp = Temp(temporary_path(output)?);
    binary.write(&tmp.0);
    if !tmp.0.exists() {
        return Err("ELF writer produced no output".into());
    }
    if let Some((header_va, header_len, _)) = unwind_header {
        let preliminary = elf::Binary::parse(&tmp.0).ok_or("cannot reparse rewritten ELF")?;
        patch_unwind_header(&tmp.0, &preliminary, base, header_va, header_len)?;
    }
    let debug_frame_offset = if let Some((_, _, content)) = &debug_frame {
        Some(append_debug_frame(&tmp.0, content)?)
    } else {
        None
    };
    fs::set_permissions(
        &tmp.0,
        fs::metadata(input)
            .map_err(|e| e.to_string())?
            .permissions(),
    )
    .map_err(|e| e.to_string())?;
    let result = elf::Binary::parse(&tmp.0).ok_or("cannot reparse rewritten ELF")?;
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
        return Err("rewritten ELF has invalid loader metadata".into());
    }
    let mut new_dynamic: Vec<_> = result
        .dynamic_symbols()
        .map(|s| (s.name(), s.value(), s.size()))
        .collect();
    new_dynamic.sort();
    if new_dynamic != old_dynamic {
        return Err("rewritten ELF changed dynamic symbols".into());
    }
    for (name, content) in old_unwind {
        if result.section_by_name(name).is_none_or(|sec| {
            sec.content() != content
                || (name == ".eh_frame" && old_eh_va.is_some_and(|va| sec.virtual_address() != va))
        }) {
            return Err(format!("rewritten ELF changed {name}"));
        }
    }
    if let Some((regions, plain, content)) = &debug_frame {
        let section = result
            .sections()
            .filter(|sec| sec.name() == ".debug_frame")
            .last()
            .ok_or("rewritten ELF has no debugger frame section")?;
        if section.get_type() != section::Type::PROGBITS
            || !section.flags().contains(section::Flags::COMPRESSED)
            || section.flags().contains(section::Flags::ALLOC)
            || section.virtual_address() != 0
            || Some(section.file_offset()) != debug_frame_offset
            || section.size() != content.len() as u64
        {
            return Err("rewritten ELF has an invalid debugger frame section".into());
        }
        let file = fs::read(&tmp.0).map_err(|e| e.to_string())?;
        let offset = usize::try_from(section.file_offset())
            .map_err(|_| "debugger frame offset out of range")?;
        let end = offset
            .checked_add(content.len())
            .ok_or("debugger frame range out of bounds")?;
        if file.get(offset..end) != Some(content.as_slice()) {
            return Err("rewritten ELF changed debugger frame data".into());
        }
        let decoded =
            miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(&content[24..], plain.len())
                .map_err(|_| "cannot decompress debugger frame data")?;
        if decoded != *plain {
            return Err("invalid debugger frame compression".into());
        }
        let frame = DebugFrame::new(plain, LittleEndian);
        let bases = BaseAddresses::default();
        let mut entries = frame.entries(&bases);
        let mut actual = Vec::new();
        while let Some(entry) = entries
            .next()
            .map_err(|e| format!("invalid debugger FDE: {e}"))?
        {
            if let CieOrFde::Fde(partial) = entry {
                let fde = partial
                    .parse(|section, bases, offset| section.cie_from_offset(bases, offset))
                    .map_err(|e| format!("invalid debugger FDE: {e}"))?;
                actual.push((fde.initial_address(), fde.end_address()));
            }
        }
        let mut expected: Vec<_> = regions
            .iter()
            .map(|region| (region.va, region.va + region.len as u64))
            .collect();
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
        return Err("rewritten ELF retains static symbols or debug sections".into());
    }
    if let Some((va, bytes)) = new_build_id
        && result.content_from_virtual_address(va, bytes.len() as u64) != bytes
    {
        return Err("rewritten ELF has an invalid build ID".into());
    }
    let new_loads: BTreeSet<u64> = result
        .segments()
        .filter(|s| s.p_type() == segment::Type::LOAD)
        .map(|s| s.virtual_address())
        .collect();
    if !old_loads.iter().all(|va| new_loads.contains(va)) {
        return Err(format!(
            "ELF writer moved an existing PT_LOAD: {old_loads:x?} -> {new_loads:x?}"
        ));
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
        return Err("rewritten ELF failed structural verification".into());
    }
    if let Some((header_va, header_len, expected)) = unwind_header {
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
            return Err("rewritten ELF has an invalid unwind header".into());
        }
        let trailer = base + layout.capacity as u64 + trailer_pad as u64;
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
        if result.content_from_virtual_address(item.patch_va, item.patch.len() as u64) != item.patch
            || (!item.retired.is_empty()
                && result.content_from_virtual_address(item.retired_va, item.retired.len() as u64)
                    != item.retired)
        {
            return Err("rewritten ELF failed entry verification".into());
        }
    }
    layout.verify_routes(&result, &image.moved, seed)?;

    let map_tmp = if let Some(path) = map {
        let tmp = Temp(temporary_path(path)?);
        let mut lines = format!("# seed 0x{seed:x}\n# old_va new_va bytes\n");
        for (&old, &new) in &image.moved {
            let len = image.lengths[&old];
            lines.push_str(&format!("0x{old:x}\t0x{new:x}\t{len}\n"));
        }
        fs::write(&tmp.0, lines).map_err(|e| e.to_string())?;
        Some(tmp)
    } else {
        None
    };

    fs::hard_link(&tmp.0, output).map_err(|e| format!("cannot create output: {e}"))?;
    if let (Some(path), Some(temp)) = (map, map_tmp.as_ref())
        && let Err(e) = fs::hard_link(&temp.0, path)
    {
        let _ = fs::remove_file(output);
        return Err(format!("cannot create map: {e}"));
    }
    let strong = selected
        .iter()
        .filter(|item| item.mode == Mode::Strong)
        .count();
    let layout_count = selected.len() - strong;
    println!(
        "rewrote {strong} strong, {layout_count} layout, {} fragments (seed 0x{seed:x}, {skipped} skipped)",
        image.moved.len()
    );
    Ok(())
}
