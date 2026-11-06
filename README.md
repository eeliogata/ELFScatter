# ELFScatter

Post-link rewriter for dynamically linked Linux x86-64 executables.

```sh
cargo build --release
./target/release/elfscatter INPUT OUTPUT
```

VM rewriting and startup decoding are on by default; `--no-vm` and `--no-startup-smc` disable them.

Unsupported functions use native routes. Output may be larger and slower. Encoding is reversible.
