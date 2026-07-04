# Testing

## Running the suite

```bash
cargo test                       # default: native-only, pure Rust
cargo test --features cvc5,z3    # also build + test the external backends (slow: vendored builds)
```

The default `default-members` set excludes the `cvc5-ff` / `z3` crates, so a
plain `cargo test` never compiles the external backends (see
[building.md](building.md)).

## The circomlib smoke test

`crates/picus/tests/r1cs_smoke.rs` runs a curated `circomlib-cff5ab6` subset
end to end through the native backend and checks each circuit's verdict. It
reads compiled `.r1cs` fixtures from the `benchmarks` git submodule.

If the fixtures are missing, the test **fails** (rather than skipping
silently) — a forgotten `git submodule update` must not slip through CI as a
green run. To provision them:

```bash
git submodule update --init benchmarks
cd benchmarks/circom && ./compile.sh build circomlib-cff5ab6
```

To run the rest of the suite locally without the submodule, opt out of just
that test:

```bash
PICUS_TEST_SKIP_SMOKE=1 cargo test
```

## Environment variables

Picus reads **no environment variables at runtime.** Every runtime knob —
solver, theory, timeout, and all native-FF engine settings — is configured
through TOML (`--config` / `./picus.toml`) or CLI flags only, layered as
built-in defaults < config file < CLI (see [usage.md](usage.md)). The
`PICUS_*` runtime overrides that existed before v1.8.1 were removed then.

The only environment variables the project reads at all are:

| Variable | Scope | Purpose |
|---|---|---|
| `PICUS_TEST_SKIP_SMOKE` | **test-only** | Skip the circomlib smoke test when the `benchmarks` submodule isn't provisioned. Compiled only into the test binary; never into `picus` / `picus-cli`. Not a runtime knob. |
| `CVC5_LIB_DIR`, `CVC5_INCLUDE_DIR`, `CVC5_DIR` | **build-time** (`--features cvc5` only) | Point the `cvc5-ff-sys` build at a prebuilt cvc5 instead of compiling it from source. See [building.md](building.md). |

Everything else the build touches (`OUT_DIR`, `CARGO_MANIFEST_DIR`, `TARGET`,
`CXXSTDLIB`, `DOCS_RS`, …) is a standard Cargo / build-system variable, not a
Picus-specific setting.
