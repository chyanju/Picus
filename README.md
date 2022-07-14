# Picus

<div align="left"><img src="https://img.shields.io/badge/tokamak-0.1-blueviolet?labelColor=blueviolet&color=3d3d3d"></div>

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
- Circom 2: https://docs.circom.io/
- Boolector: https://boolector.github.io/
  - recommended for faster solving, if not, z3 will be used (may be slower)



## Commands

```
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

# test on ecne example
racket ./run-ecne-equivalence.rkt --cname AND@gates

# push-button example for equivalence checking
racket ./test-push-button-equivalence.rkt
# turn on error tracing (for debugging)
racket -l errortrace -t ./test-push-button-equivalence.rkt

# example test for the r1cs utilities
racket ./test-read-r1cs.rkt

# automatic uniqueness checking
racket ./test-uniqueness.rkt

# grab Ecne's readable constraints only
julia --project=. src/gen_benchmark.jl Circom_Functions/benchmarks/bigmod_5_2.r1cs > Circom_Functions/benchmarks/bigmod_5_2.txt

# calling Ecne
circom -o ./target/ ./ecne_circomlib_tests/ooo.circom --r1cs --sym --O0
julia --project=. src/Ecne.jl --r1cs target/ooo.r1cs --name oooo --sym target/ooo.sym
```

## Notes

- The current R1CS parser is a stricter version that only allows 3 sections of type 1, 2 and 3 only. For the parser that complies with the currently very loose spec of R1CS (https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md), please see `r1cs-ext.rkt`. To have better control of the prototype, the stricter version is used instead.
- Ecne's wire id starts from 1: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1683
- Ecne's readable outputs are "unoptimized". To compare the outputs with Ecne, you need to comment out the "unoptimizing" snippet of Ecne.

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
