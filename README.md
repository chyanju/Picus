# Picus

<div align="left">
    The symbolic compilation follows the <img src="https://img.shields.io/badge/tokamak-0.1-blueviolet?labelColor=blueviolet&color=3d3d3d"> pattern.
</div>

## Requirements

- Racket (8.0+): [https://racket-lang.org/](https://racket-lang.org/)
  - Rosette (4.0+): [https://github.com/emina/rosette](https://github.com/emina/rosette)
    - `raco pkg install rosette`
  - csv-reading: [https://www.neilvandyke.org/racket/csv-reading/](https://www.neilvandyke.org/racket/csv-reading/)
    - `raco pkg install csv-reading`
- Circom 2: [https://docs.circom.io/](https://docs.circom.io/)
- Rust: [https://www.rust-lang.org/](https://www.rust-lang.org/)
  - for circom parser


## Commands

```bash
# build circom parser
cd circom-parser
cargo build

# use circom parser
./circom-parser/target/debug/parser ./examples/test1.circom
./circom-parser/target/debug/parser ./examples/test1.circom > ./examples/test1.json

# example test for the r1cs utilities
racket ./test-read-r1cs.rkt

# automatic uniqueness checking
racket ./test-uniqueness.rkt

# automatic equivalence checking
racket ./test-equivalence.rkt

# simple circom compilation command
# circom ./test0.circom --r1cs --wasm --sym --c
circom -o ./examples/ ./examples/test1.circom --r1cs --sym

# grab Ecne's readable constraints only
julia --project=. src/gen_benchmark.jl Circom_Functions/benchmarks/bigmod_5_2.r1cs > Circom_Functions/benchmarks/bigmod_5_2.txt
```

## Known Issues

- `NOT@gates.circom` is generating a potentially buggy r1cs file.
- `MultiAND@gates.circom`: pending.

## Notes

- The current R1CS parser is a stricter version that only allows 3 sections of type 1, 2 and 3 only. For the parser that complies with the currently very loose spec of R1CS ([https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)), please see `r1cs-ext.rkt`. To have better control of the prototype, the stricter version is used instead.
- Ecne's wire id starts from 1: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1683](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1683)
- Ecne's readable outputs are "unoptimized". To compare the outputs with Ecne, you need to comment out the "unoptimizing" snippet of Ecne.

## Resources

- Parsing a circuit into AST: [https://circom.party/](https://circom.party/)
- R1CS Binary Format: [https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)
  - Wire 0 must be always mapped to label 0 and it's an input forced to value "1" implicitly
  - ~~--> Here the current impl. follows Ecne (in Julia), so it starts from 1.~~ Now this tool starts from 0 following the original r1cs spec.
- GF example meaning: [https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7](https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7)
- Ecne's benchmarks
  - [https://github.com/franklynwang/EcneProject/tree/master/ecne_circomlib_tests](https://github.com/franklynwang/EcneProject/tree/master/ecne_circomlib_tests)
- Ecne's `readR1CS`: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1626](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1626)
- Ecne's `printEquation`: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L424](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L424)
- Ecne's r1cs->string: [https://github.com/franklynwang/EcneProject/blob/master/src/gen_benchmark.jl](https://github.com/franklynwang/EcneProject/blob/master/src/gen_benchmark.jl)
