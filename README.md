<div align="left">
  <h1>
    <img src="./resources/picus-white.png" width=50>
  	Picus
  </h1>
</div>
Picus is a symbolic virtual machine for automated verification tasks on R1CS.

## Building from Docker

```bash
docker build -t picus:v0 .
docker run -it --rm picus:v0 bash
```

## Dependencies (Building from Source)

- Racket (8.0+): https://racket-lang.org/
  - Rosette (4.0+): https://github.com/emina/rosette
    - `raco pkg install rosette`
  - csv-reading: https://www.neilvandyke.org/racket/csv-reading/
    - `raco pkg install csv-reading`
- Rust: https://www.rust-lang.org/
  - for circom parser
- Node.js: https://nodejs.org/en/
  - for circom parser
- Circom (2.0.6 Required): https://docs.circom.io/
  - older version may touch buggy corner cases

- z3 solver (4.10.2+ Required): [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)
  - older version may touch buggy corner cases

- cvc5-ff: [https://github.com/alex-ozdemir/CVC4/tree/ff](https://github.com/alex-ozdemir/CVC4/tree/ff)
  - see installation instructions [here](./NOTES.md#installing-cvc5-ff)

## Usage

> Note: Picus is under development, so there are several experimental versions for the purpose of comparison. The larger the version number, the most recent the version. Ideally you should try to use the most recent version.

> WIP: Lemmas applied in different versions may be different. We are working on a unified interface to it.

### Constraint Preparations

Note: To run the uniqueness checking on benchmarks included (circom files), you'll need to prepare them (compiling to r1cs files) first, by running:

```bash
./script/prepare-??.sh
```

where `??` corresponds to corresponding benchmark set label.

### V0: Naive Version

This version directly issues the raw constraints to the solver (with some simple optimizations to the constraints to make it more readable by the user).

```bash
usage: test-v0-uniqueness.rkt [ <option> ... ]
<option> is one of
  --r1cs <p-r1cs> path to target r1cs
  --solver <p-solver> solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout> timeout for every small query (default: 5000ms)
  --smt show path to generated smt files (default: false)
  --help, -h Show this help
```

### V1: Naive Slicing Version

This builds on top of v0 version. This version incorporates the slicing features where each time only one key variable's uniqueness property is queried. The core algorithm is located at `picus/algorithms/inc.rkt`.

```bash
usage: test-v1-uniqueness.rkt [ <option> ... ]
<option> is one of
  --r1cs <p-r1cs> path to target r1cs
  --solver <p-solver> solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout> timeout for every small query (default: 5000ms)
  --smt show path to generated smt files (default: false)
  --help, -h Show this help
```

### V2: Propagation & Preserving Version

This builds on top of v1 version. This version incorporates a propagation procedure of the uniqueness property between two slicing queries so as to improve scalability. The core algorithm is located at `picus/algorithms/pp.rkt`.

```bash
usage: test-v2-uniqueness.rkt [ <option> ... ]
<option> is one of
  --r1cs <p-r1cs> path to target r1cs
  --solver <p-solver> solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout> timeout for every small query (default: 5000ms)
  --initlvl <p-initlvl> initial level of neighboring method: 0 - full nb | 1 | 2 - disable nb (default:0)
  --smt show path to generated smt files (default: false)
  --weak only check weak safety, not strong safety  (default: false)
  --help, -h Show this help
```

### V3: Propagation & Preserving with Neighboring Version

This builds on top of v2 version. This version incorporates neighboring checking to narrow down the search scope, which will improve the performance if the ground truth of a circuit is safe. The core algorithm is located at `picus/algorithms/nb.rkt`. Note that the current neighboring version also has propagation & preserving version built inside.

```bash
usage: test-v3-uniqueness.rkt [ <option> ... ]
<option> is one of
  --r1cs <p-r1cs> path to target r1cs
  --solver <p-solver> solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout> timeout for every small query (default: 5000ms)
  --initlvl <p-initlvl> initial level of neighboring method: 0 - full nb | 1 | 2 - disable nb (default:0)
  --smt show path to generated smt files (default: false)
  --weak only check weak safety, not strong safety  (default: false)
  --help, -h Show this help
```

## Example Commands

```bash
# example test for the r1cs utilities
racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib-cff5ab6/EscalarMulAny@escalarmulany.r1cs

# check uniqueness using slicing, using cvc5
# timeout is 3s, output and show path to smt
racket ./test-v1-uniqueness.rkt --r1cs ./benchmarks/circomlib-cff5ab6/Mux4@mux4.r1cs --timeout 3000 --smt --solver cvc5

# prepare a set of benchmarks (run from repo root)
./scripts/prepare-iden3-core.sh
```

## Other Commands

```bash
# build circom parser
cd circom-parser
cargo build

# use circom parser
./circom-parser/target/debug/parser ./examples/test10.circom > ./examples/test10.json
./circom-parser/target/debug/parser ./benchmarks/ecne/Num2BitsNeg@bitify.circom > ./benchmarks/ecne/Num2BitsNeg@bitify.json

# simple circom compilation command
# circom ./test0.circom --r1cs --wasm --sym --c
circom -o ./examples/ ./examples/test10.circom --r1cs --sym
circom -o ./benchmarks/ecne/ ./benchmarks/ecne/Num2BitsNeg@bitify.circom --r1cs --sym

# grab Ecne's readable constraints only
julia --project=. src/gen_benchmark.jl Circom_Functions/benchmarks/bigmod_5_2.r1cs > Circom_Functions/benchmarks/bigmod_5_2.txt

# calling Ecne
circom -o ./target/ ./ecne_circomlib_tests/ooo.circom --r1cs --sym --O0
julia --project=. src/Ecne.jl --r1cs target/ooo.r1cs --name oooo --sym target/ooo.sym
```

## Potential Issues

- "too many open files" errors, see [https://github.com/davidemms/OrthoFinder/issues/384](https://github.com/davidemms/OrthoFinder/issues/384)

## Resources

- Parsing a circuit into AST: https://circom.party/
- R1CS Binary Format: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md
  - Wire 0 must be always mapped to label 0 and it's an input forced to value "1" implicitly
- GF example meaning: https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7
- Ecne's benchmarks
  - https://github.com/franklynwang/EcneProject/tree/master/ecne_circomlib_tests
- Ecne's `readR1CS`: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1626
- Ecne's `printEquation`: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L424
- Ecne's r1cs->string: https://github.com/franklynwang/EcneProject/blob/master/src/gen_benchmark.jl
