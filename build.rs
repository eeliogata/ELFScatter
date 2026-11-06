use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn command(variable: &str, default: &str) -> Command {
    println!("cargo:rerun-if-env-changed={variable}");
    let mut command = Command::new(env::var_os(variable).unwrap_or_else(|| default.into()));
    command.env("LC_ALL", "C");
    command
}

fn output(command: &mut Command) -> Result<String, String> {
    let result = command.output().map_err(|e| format!("{command:?}: {e}"))?;
    if !result.status.success() {
        return Err(format!(
            "{command:?}: {}\n{}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    String::from_utf8(result.stdout).map_err(|e| e.to_string())
}

fn build() -> Result<(), String> {
    let host = env::var("HOST").map_err(|e| e.to_string())?;
    let target = env::var("TARGET").map_err(|e| e.to_string())?;
    if host != target || target != "x86_64-unknown-linux-gnu" {
        return Err(
            "the VM runtime requires a native x86_64-unknown-linux-gnu build with GCC and binutils"
                .into(),
        );
    }
    for path in ["src/vm_runtime.c", "src/vm_runtime.S", "src/vm_abi.h"] {
        println!("cargo:rerun-if-changed={path}");
    }
    let out = PathBuf::from(env::var_os("OUT_DIR").ok_or("OUT_DIR is unset")?);
    let header = fs::read_to_string("src/vm_abi.h").map_err(|e| e.to_string())?;
    let mut constants = String::new();
    let mut opcode = false;
    for line in header.lines() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.len() != 3 || words[0] != "#define" {
            return Err("invalid VM ABI definition".into());
        }
        let value: usize = words[2].parse().map_err(|_| "invalid VM ABI value")?;
        opcode |= words[1] == "VM_PUSH_REG";
        let ty = if opcode { "u8" } else { "usize" };
        constants.push_str(&format!(
            "#[allow(dead_code)]\nconst {}: {ty} = {value};\n",
            words[1]
        ));
    }
    fs::write(out.join("vm_abi.rs"), constants).map_err(|e| e.to_string())?;
    let c0 = out.join("vm_runtime_c0.o");
    let c1 = out.join("vm_runtime_c1.o");
    let asm = out.join("vm_runtime_asm.o");
    let elf = out.join("vm_runtime.elf");
    let binary = out.join("vm_runtime.bin");
    let script = out.join("vm_runtime.ld");
    fs::write(&script, "SECTIONS { . = 0; .vmruntime : { *(.vmruntime) *(.text .text.*) *(.rodata .rodata.*) } /DISCARD/ : { *(.eh_frame*) *(.note*) *(.comment) *(.gnu*) } }\n").map_err(|e| e.to_string())?;
    for (variant, object) in [(0, &c0), (1, &c1)] {
        output(
            command("CC", "gcc")
                .arg(format!("-DVM_VARIANT={variant}"))
                .arg(format!("-Dvm_run=vm_run_{variant}"))
                .args([
                    "-O3",
                    "-m64",
                    "-march=x86-64",
                    "-fPIC",
                    "-ffreestanding",
                    "-fno-builtin",
                    "-fno-stack-protector",
                    "-fno-asynchronous-unwind-tables",
                    "-fno-unwind-tables",
                    "-fno-jump-tables",
                    "-fno-tree-vectorize",
                    "-fno-plt",
                    "-ffixed-r15",
                    "-mno-red-zone",
                    "-mgeneral-regs-only",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-Wstack-usage=1024",
                    "-c",
                    "src/vm_runtime.c",
                    "-o",
                ])
                .arg(object),
        )?;
    }
    output(
        command("CC", "gcc")
            .args(["-m64", "-c", "src/vm_runtime.S", "-o"])
            .arg(&asm),
    )?;
    output(
        command("LD", "ld")
            .args(["-nostdlib", "--no-undefined", "-T"])
            .arg(&script)
            .arg("-o")
            .arg(&elf)
            .arg(&asm)
            .arg(&c0)
            .arg(&c1),
    )?;
    let bytes = fs::read(&elf).map_err(|e| e.to_string())?;
    if bytes.get(..6) != Some(b"\x7fELF\x02\x01") || bytes.get(18..20) != Some(&[62, 0]) {
        return Err("VM compiler produced an incompatible ELF".into());
    }
    let relocations = output(command("READELF", "readelf").arg("-r").arg(&elf))?;
    if !relocations.contains("There are no relocations") {
        return Err("VM runtime contains relocations".into());
    }
    let sections = output(command("READELF", "readelf").args(["-SW"]).arg(&elf))?;
    let mut runtime = None;
    for line in sections.lines() {
        let Some((_, fields)) = line.split_once(']') else {
            continue;
        };
        let fields: Vec<_> = fields.split_whitespace().collect();
        if fields.len() < 7 || !fields[6].contains('A') {
            continue;
        }
        if fields[0] != ".vmruntime"
            || fields[1] != "PROGBITS"
            || fields[6] != "AX"
            || runtime.is_some()
        {
            return Err(format!("unexpected allocated VM section: {line}"));
        }
        let address = usize::from_str_radix(fields[2], 16).map_err(|e| e.to_string())?;
        let offset = usize::from_str_radix(fields[3], 16).map_err(|e| e.to_string())?;
        let size = usize::from_str_radix(fields[4], 16).map_err(|e| e.to_string())?;
        let end = offset.checked_add(size).ok_or("VM section size overflow")?;
        if address != 0 || size == 0 || end > bytes.len() {
            return Err("VM code section has invalid bounds".into());
        }
        runtime = Some(offset..end);
    }
    let runtime = runtime.ok_or("VM code section missing")?;
    output(
        command("OBJCOPY", "objcopy")
            .args(["-O", "binary", "--only-section=.vmruntime"])
            .arg(&elf)
            .arg(&binary),
    )?;
    let extracted = fs::read(&binary).map_err(|e| e.to_string())?;
    if extracted != bytes[runtime] {
        return Err("extracted VM runtime differs from its ELF section".into());
    }
    let symbols = output(command("NM", "nm").arg("-n").arg(&elf))?;
    let mut constants = String::new();
    let mut previous = None;
    let mut implementations = [0; 2];
    for symbol in [
        "vm_enter",
        "vm_context_ready",
        "vm_native_enter",
        "vm_native_restored",
        "vm_native_leave",
        "vm_finish",
        "vm_finish_restored",
        "vm_return",
        "vm_tail",
        "vm_tail_restored",
        "vm_tail_jump",
        "vm_abort",
        "vm_run",
        "vm_run_0",
        "vm_run_1",
    ] {
        let mut matches = symbols
            .lines()
            .filter(|line| line.split_whitespace().last() == Some(symbol));
        let line = matches
            .next()
            .ok_or_else(|| format!("missing VM symbol {symbol}"))?;
        if matches.next().is_some() || line.split_whitespace().nth(1) != Some("T") {
            return Err(format!("invalid VM code symbol {symbol}"));
        }
        let number = line.split_whitespace().next().ok_or("missing VM address")?;
        let address = usize::from_str_radix(number, 16).map_err(|e| e.to_string())?;
        if address >= extracted.len()
            || previous.is_some_and(|last| address <= last)
            || (symbol == "vm_enter" && address != 0)
        {
            return Err(format!("VM symbol {symbol} has invalid offset {address}"));
        }
        previous = Some(address);
        match symbol {
            "vm_run_0" => implementations[0] = address,
            "vm_run_1" => implementations[1] = address,
            _ => constants.push_str(&format!(
                "const {}_OFF: usize = {address};\n",
                symbol.to_uppercase()
            )),
        }
    }
    if extracted[implementations[0]..implementations[1]] == extracted[implementations[1]..] {
        return Err("VM implementations are identical".into());
    }
    fs::write(out.join("vm_runtime_offsets.rs"), constants).map_err(|e| e.to_string())?;
    Ok(())
}

fn main() {
    if let Err(error) = build() {
        eprintln!("elfscatter runtime build: {error}");
        std::process::exit(1);
    }
}
