# ELFScatter

Rewrites functions in dynamically linked Linux x86-64 executables. It moves fragments into a new RX `PT_LOAD`, scatters their branch records and handlers, and patches the original entries. Paired branches can carry an unused route.

```sh
cargo build --release
./target/release/elfscatter inspect ./program
./target/release/elfscatter rewrite ./program -o ./program.scattered
```

With no selector, `rewrite` scans sized function symbols and unwind FDE ranges. Use repeated `--symbol NAME` to pick functions, `--exclude NAME` to omit one, or `--address 0xVA --size N` to pick a range. `--seed N` fixes the layout. `--map FILE` writes fragment addresses.

Strong routing uses R10 and R11. `--layout-fallback` uses direct branches for functions ineligible for strong routing. `--no-dispatch` uses direct branches throughout. `--scrub trap|random|off` controls the old code. `--keep-metadata` retains static symbols, debug sections, and the build ID.

Selected functions are limited to 1 MiB. The writer rejects indirect jumps, body relocations, incoming interior references, and unwind data with LSDA, personality routines, or unsupported rules. Runtime unwinding uses a rebuilt `.eh_frame_hdr`. Moved code with unwind data gets a compressed `.debug_frame` for GDB.
