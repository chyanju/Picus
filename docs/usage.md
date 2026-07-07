# Usage

Full command-line and configuration reference. For a quick start see the
[README](../README.md); for building the optional cvc5 / z3 backends see
[building.md](building.md).

## `picus check` — verify circuit uniqueness

```bash
picus check --r1cs circuit.r1cs                              # default: native + ff
picus check --r1cs circuit.r1cs --solver cvc5 --theory ff    # cvc5 (build with --features cvc5)
picus check --r1cs circuit.r1cs --solver z3 --theory nia     # z3 over the integers (--features z3)
picus check --r1cs circuit.r1cs --solver none                # propagation only
picus check --r1cs circuit.r1cs --lemmas all-bim             # all lemmas except bim
picus check --r1cs circuit.r1cs --format json                # JSON output
picus check --r1cs circuit.r1cs --dump-smt /tmp/smt/         # dump SMT queries
```

| Flag | Default | Description |
|------|---------|-------------|
| `--r1cs <path>` | *required* | R1CS binary file |
| `--config <path>` | `./picus.toml` if present | TOML config file (see [Configuration](#configuration)); flags below override it |
| `--solver <name>` | `native` | Backend: `native`, `cvc5`, `z3`, `none` (`cvc5`/`z3` require their Cargo features). Names resolve against the inventory of registered backends |
| `--theory <ff\|nia>` | `ff` | `ff` (finite field) or `nia` (integer mod) |
| `--timeout <ms>` | `5000` | Per-query solver timeout |
| `--selector <first\|counter>` | `counter` | Signal selection heuristic |
| `--lemmas <spec>` | `all` | `all`, `none`, `all-X,Y` (exclude), `none+X,Y` (include). Names are validated against the live registry (an unknown name lists the valid ones); see [lemmas.md](lemmas.md) |
| `--format <human\|json>` | `human` | Output format |
| `--dump-smt <dir>` | — | Dump SMT-LIB queries to a directory |
| `--profile <none\|wall>` | `none` | Emit per-site wall-clock profile to stderr |
| `--gb-strategy <direct\|by-homog\|auto>` | `direct` | GB algorithm: direct Buchberger / homogenisation pipeline / auto-pick by homogeneity test (`native` only). Matches the `gb_strategy` config key. (`--gb-by-homog <off\|on\|auto>` is a deprecated alias.) |

### Advanced / research flags

| Flag | Default | Description |
|------|---------|-------------|
| `--poly-repr <sparse\|dense>` | `sparse` | Polynomial representation (`native`): `sparse` scales on wide rings, `dense` is faster on narrow rings |
| `--use-f4 [on\|off]` | off | F4 matrix reduction for batched same-sugar S-pairs (`native`, dense engine only). Bare flag = on; `off` overrides a config file |
| `--dnf [on\|off]` | off | Pick DNF instead of CNF for the boolean layer (`native`). Bare flag = on |
| `--dnf-cap <N>` | `100000` | DNF expansion cap; returns `unknown` beyond this disjunct count |
| `--cdclt-iter-cap <N>` | `1000000` | CDCL(T) outer-iteration cap |
| `--gb-stats [on\|off]` | off | Emit per-run GB statistics to stderr (`native`). Bare flag = on |
| `--gb-trace [on\|off]` | off | Emit GB trace events to stderr (`native`). Bare flag = on |
| `--cache <on\|off>` | on | The native FF backend's incremental Buchberger cache between successive `solve()` calls (`--no-cache` = shorthand for `off`). Cache-off solves run the dense-only traced pipeline, so this also changes engine routing, not just cache reuse |
| `--aboz-disj <on\|off>` | on | The `aboz` lemma's entailed zero-product disjunctions (`--no-aboz-disj` = shorthand for `off`) |
| `--linear-elim [on\|off]` | off | Linear (Gaussian) pre-elimination before solving (`native`); may help linear-heavy circuits. Bare flag = on. Runs inside the `--timeout` budget |
| `--split-triangular <on\|off>` | off | Triangular model construction for a zero-dimensional combined system on the split-GB path, in place of the brancher DFS (`native`) |
| `--membership-fastpath <on\|off>` | on | Ideal-membership Safe fast-path for uniqueness queries on the cached split-GB path: reduce `x_a − x_b` against the constraint-side basis and return UNSAT directly on a zero remainder (`native`) |
| `--radical-membership <on\|off>` | off | Monolithic-GB radical Safe fast-path: whole-ring test on the GB of `I ∪ {(x_a−x_b)·w − 1}`, catching forced-equal outputs the partition reduction misses; bounded by a sub-budget (`native`) |
| `--matrix-elim-order <on\|off>` | off | Build the solve ring under the alt-copy elimination order instead of DegRevLex; shapes the stages around the GB core (`native`) |
| `--dynamic-order <on\|off>` | on | Size-adaptive term order: alt-copy elimination order on rings of ≥ `DYNAMIC_ORDER_MIN_VARS` variables, DegRevLex below (`native`) |
| `--zech-log-small-fp <on\|off>` | off | Zech (discrete-log) multiply/inverse/power tables for primes ≤ 2^20; result-identical, small-prime path only (`native`) |
| `--reducer-index-cache <on\|off>` | off | Cache the reducer's divisor index across reductions with an unchanged active basis (dense engine only) (`native`) |
| `--frobenius-cache <on\|off>` | on | Memoize `x^p mod poly` across Cantor–Zassenhaus calls on the same `(prime, poly)` (`native`) |
| `--branching-incremental-gb <on\|off>` | on | Extend the parent GB with the single branching constraint via `compute_gb_incremental_with_order` instead of recomputing the full basis at each DFS branch (`native`) |
| `--cdclt-multi-prime-router <on\|off>` | off | Route CDCL(T) facts through `cdclt::multi_prime::FfTheoryRouter` (single-slot when input is single-prime; multi-slot when fed by `parse_boolean_multi`) (`native`) |
| `--cdclt-equality-engine <on\|off>` | off | Interpose `cdclt::equality_engine::EqualityEngine` before the FF theory; drops canonical-polynomial duplicate facts and surfaces precise 2-literal lemmas on polarity contradictions (`native`) |
| `--cdclt-incremental-theory <on\|off>` | off | Route CDCL(T) through `cdclt::ff_theory_incremental::IncrementalFfTheoryState`; carries an `IncrementalGB` across SAT decisions, with model extraction via a user-namespaced facade ring (`native`) |
| `--uf-enabled <on\|off>` | on | Uninterpreted-function (UF) support (`native`). Consulted only when a query carries UF applications; `off` refuses them with a typed Unknown instead of dropping the congruence constraints |
| `--uf-pair-cap <N>` | 4096 | Max same-symbol UF application pairs expanded per solve (`native`). `0` = immediate Unknown; overflow of a nonzero cap continues degraded (Unsat sound; Sat requires function-table certification) |
| `--uf-closure <on\|off>` | on | Cached-path UNSAT-only congruence-closure probe for UF-bearing queries (`native`). Never produces Sat |
| `--uf-mode <lazy\|ackermann>` | lazy | Decision procedure on the CDCL(T) route for UF-bearing queries (`native`): congruence-closure equality hub vs eager Ackermann expansion (fallback). The DNF route always Ackermannizes |
| `--f4-hilbert-select <on\|off>` | on | BCR Hilbert-driven F4 batch selection (`HilbertNum::add_generators_incremental` per candidate; inert when `--use-f4` is off) (`native`) |
| `--f4-sparse-reducer-cache <on\|off>` | on | Sparse-row reducer cache inside `F4Workspace`: stores basis index only, rematerialises the reducer at hit time (inert when `--use-f4` is off) (`native`) |

> `z3 + ff` is rejected (z3 has no finite-field theory); `native + nia` is
> rejected (the native backend implements only QF_FF).

## `picus info` — inspect R1CS metadata

```bash
picus info --r1cs circuit.r1cs
picus info --r1cs circuit.r1cs --constraints   # also print every constraint
```

## Configuration

Every knob has a built-in default, so no configuration is required. When you
do want to pin settings, Picus resolves them in three layers, each overriding
only the keys it sets (later wins):

1. **Built-in defaults** — compiled in; what a library import (`Config::default()`) and a flagless CLI run get. No file is read.
2. **Config file** — the TOML passed to `--config <FILE>`, or `./picus.toml` in the working directory when present. A missing *explicit* `--config` file is an error; a missing `./picus.toml` is skipped silently.
3. **CLI flags** — highest precedence.

[`picus.default.toml`](../picus.default.toml) at the repo root documents every
key at its default value — copy it and edit. Keys are split into two tables:

- `[analysis]` — `solver`, `theory`, `timeout_ms`, `selector`, `lemmas`, `dump_smt`, and the lemma toggle `aboz_emit_disjunctions`. Backend-agnostic.
- `[engine]` — Picus's in-tree engine: the native FF Gröbner solver knobs (`gb_strategy`, `use_f4`, `dnf_enabled`, `dnf_cap`, `cdclt_iter_cap`, `cache_enabled`, `linear_elim`, `split_triangular`, `membership_fastpath`, `radical_membership`, `matrix_elim_order`, `dynamic_order`, `zech_log_small_fp`, `reducer_index_cache`, `frobenius_cache`, `branching_incremental_gb`, `cdclt_multi_prime_router`, `cdclt_equality_engine`, `cdclt_incremental_theory`, `f4_hilbert_select`, `f4_sparse_reducer_cache`, `uf_enabled`, `uf_pair_cap`, `uf_closure`, `uf_mode`) plus the IR knob that also shapes the cvc5 path (`poly_repr`) and the diagnostics (`gb_stats_enabled`, `gb_trace_enabled`, `profile_enabled`). The native-solver-only keys are unused when delegating to cvc5 / z3.

```toml
[analysis]
solver = "native"
timeout_ms = 10000

[engine]
poly_repr = "sparse"
gb_strategy = "auto"
```

An unknown key is a hard error. As a library, `PicusConfig::from_file("picus.toml")`
applies a file over the defaults, while `PicusConfig::default()` stays zero-I/O.

## Interpreting results

| Result | Meaning |
|--------|---------|
| **safe** | All output signals are proven uniquely determined by the inputs. No false positives — if Picus says safe, the outputs are safe. |
| **unsafe** | A concrete counter-example was found: two distinct valid witnesses sharing the same public inputs but differing on an output. Shown as two witnesses. |
| **unknown** | The solver could not decide within the timeout. Not a safety claim either way — analysis was inconclusive. A larger `--timeout` or a different solver may help. |

## Solver differences

| Backend | Theory | How it works |
|---------|--------|--------------|
| native + QF_FF *(default)* | Finite field | Pure-Rust in-tree Gröbner-basis engine; no external solver or C++ dependency |
| cvc5 + QF_FF | Finite field | cvc5's CoCoA / Gröbner-basis FF solver (`--features cvc5`) |
| z3 + QF_NIA | Integer mod p | Integer arithmetic with explicit `mod p` (`--features z3`) |
| none | — | Propagation only; no SMT solver invoked |

The QF_FF and QF_NIA encodings are semantically equivalent: if two backends
terminate, they should agree on safe/unsafe.

- **Both safe** / **both unsafe** — consistent.
- **One safe, one unknown** — normal; the unknown backend timed out. Trust the one that terminated.
- **One safe, one unsafe** — should not happen with correct encodings. Verify the counter-example manually (check that both witnesses satisfy every R1CS constraint); the backend reporting unsafe may have a soundness issue, or there is an encoding discrepancy.

> **Known cvc5 issue**: cvc5 1.2.0–1.3.3 can produce spurious SAT with
> inconsistent models for `or` disjunctions in QF_FF. Picus's lowering
> avoids emitting `or`-shaped queries, so this does not affect normal usage.

## Library API: build and solve a `PolyIR`

Beyond the R1CS uniqueness pipeline (`check_circuit` / `check_r1cs`), the
`picus` crate exposes `picus::PolyIR` — an ergonomic builder for an arbitrary
polynomial constraint system over GF(p). You declare variables by name, write
constraints with ordinary Rust operators, and `solve()`. There is **no** R1CS
and **no** uniqueness / two-copy semantics: the query means exactly what its
constraints say, and the result is `Unsat` / `Sat(model)` / `Unknown(reason)`.
The low-level ring / `Arc` / polynomial machinery is hidden.

```rust
use picus::PolyIR;

let mut pir = PolyIR::new(7u32);          // GF(7); accepts u32/u64/BigUint
let [x, y] = pir.vars(["x", "y"]);        // named, Copy handles

pir.eq(x * x - x, 0);                     // x*x - x == 0   (pins x ∈ {0, 1})
pir.eq(y, 1);                             // y == 1
pir.ne(x, y);                             // x != y         (⇒ x = 0)
pir.field_polys(true);                    // exact reasoning over the small prime

match pir.solve().unwrap() {
    picus::Solution::Sat(m) => {
        println!("x = {}", m.u64(x).unwrap());   // 0   — lookup by handle
        println!("y = {}", m["y"]);              // 1   — or by name
    }
    picus::Solution::Unsat        => println!("unsatisfiable"),
    picus::Solution::Unknown(why) => println!("undecided: {why:?}"),
}
```

**Expressions.** `Var` is `Copy`, so variables plug straight into `+ - *`
without `&`; constants are plain integers. All of these build the same
`Expr`: `x * x`, `2 * x + 3`, `x.pow(3)`, `-x`, `2*x + 3*y - 5`, `x - 1`.
Because Rust's `==` / `!=` must return `bool`, (dis)equality is expressed with
the **methods** `pir.eq(lhs, rhs)` / `pir.ne(lhs, rhs)` (and `x.equals(rhs)`),
not the operators.

**Constraints.** `eq(l, r)` / `ne(l, r)` (any expressions — `ne(x*x, 2)` works),
`assign(var, value)` (pin a variable), `or([c1, c2, …])` (disjunction of
`== 0` clauses), `bitsum([b0, b1, …])`, and `field_polys(bool)`.

**Solving.** `pir.solve()` uses the defaults; `pir.solve_with(config)` takes a
[`PicusConfig`](#configuration) — `config.analysis.solver` / `.theory` pick the
backend (default `native` + `ff`), `.timeout_ms` bounds each call, and
`config.engine` tunes the native FF engine.

**Model.** `m[x]` (by handle) or `m["x"]` (by name) return the `BigUint` value;
`m.u64(x)` is a convenience; `m.iter()` yields the user variables (auxiliary
variables are hidden). Power users can drop to the raw lowered form with
`pir.lower()`.

**Soundness / completeness.** The native FF backend is sound. Its completeness
depends on the field polynomials `x^p - x = 0`: call `field_polys(true)` for
exact reasoning over small primes (the encoder materialises them only for
`prime <= 1000`). Over cryptographic primes it is sound-but-incomplete —
`Unsat` is trustworthy, a returned `Sat` model is re-validated before it is
handed back, and queries it cannot decide come back `Unknown`.

## Troubleshooting

**Killed / out of memory.** Large circuits can consume significant memory
during the solve. Under Docker, raise the container memory limit. On the
native backend, `--poly-repr sparse` (the default) keeps wide rings compact.

**Solver hangs / reports `unknown`.** The query was too hard within the
timeout. Options:

- Increase `--timeout` (e.g. `--timeout 60000`).
- Try another backend (`--solver z3 --theory nia`, or `--solver cvc5 --theory ff` if built with `--features cvc5`).
- `--solver none` to see how far propagation alone gets.
- On `native + ff`: `--gb-strategy auto` routes through the homogenisation GB pipeline that wins on bit-decomposition-shaped ideals; `--use-f4` enables the F4 matrix path (research flag).
