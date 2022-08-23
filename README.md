<div align="left">
  <h1>
    <img src="./resources/picus-white.png" width=50>
  	Picus
  </h1>
</div>
Picus is a symbolic virtual machine for automated verification tasks on R1CS.

## Dependencies

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

### Normal Version

```bash
usage: test-uniqueness.rkt [ <option> ... ]

<option> is one of

  --r1cs <p-r1cs>
     path to target r1cs
  --solver <p-solver>
     solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout>
     timeout for every small query (default: 5000ms)
  --smt
     show path to generated smt files (default: false)
  --help, -h
     Show this help
  --
     Do not treat any remaining argument as a switch (at this level)

 Multiple single-letter switches can be combined after
 one `-`. For example, `-h-` is the same as `-h --`.
```

### Slicing Version

```bash
usage: test-inc-uniqueness.rkt [ <option> ... ]

<option> is one of

  --r1cs <p-r1cs>
     path to target r1cs
  --solver <p-solver>
     solver to use: z3 | cvc5 (default: z3)
  --timeout <p-timeout>
     timeout for every small query (default: 5000ms)
  --smt
     show path to generated smt files (default: false)
  --help, -h
     Show this help
  --
     Do not treat any remaining argument as a switch (at this level)

 Multiple single-letter switches can be combined after
 one `-`. For example, `-h-` is the same as `-h --`.
```

## Example Commands

```bash
# example test for the r1cs utilities
racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib/EscalarMulAny@escalarmulany.r1cs

# check uniqueness in one shot, using z3 solver
# timeout is 10s, output and show path to smt
racket ./test-uniqueness.rkt --r1cs ./benchmarks/circomlib/Bits2Num@bitify.r1cs --timeout 10000 --smt --solver z3

# check uniqueness using slicing, using cvc5
# timeout is 3s, output and show path to smt
racket ./test-inc-uniqueness.rkt --r1cs ./benchmarks/circomlib/Mux4@mux4.r1cs --timeout 3000 --smt --solver cvc5
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
