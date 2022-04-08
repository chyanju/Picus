# Picus
Equivalence Verification for R1CS

## Commands

```bash
# example test for the r1cs utilities
racket ./test-read-r1cs.rkt

# simple circom compilation command
circom ./test0.circom --r1cs --wasm --sym --c

# grab Ecne's readable constraints only
julia --project=. src/gen_benchmark.jl Circom_Functions/benchmarks/bigmod_5_2.r1cs > Circom_Functions/benchmarks/bigmod_5_2.txt
```

## Notes

- The current R1CS parser is a stricter version that only allows 3 sections of type 1, 2 and 3 only. For the parser that complies with the currently very loose spec of R1CS ([https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)), please see `r1cs-ext.rkt`. To have better control of the prototype, the stricter version is used instead.
- Ecne's wire id starts from 1: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1683](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1683)
  - Could be aligning with r1cs spec since `wireID_1` is the first in the spec?
- Ecne's readable outputs are "unoptimized". To compare the outputs with Ecne, you need to comment out the "unoptimizing" snippet of Ecne.

## Resources

- R1CS Binary Format: [https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)
- GF example meaning: [https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7](https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7)
- Ecne's `readR1CS`: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1626](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L1626)

- Ecne's `printEquation`: [https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L424](https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L424)

- Ecne's r1cs->string: [https://github.com/franklynwang/EcneProject/blob/master/src/gen_benchmark.jl](https://github.com/franklynwang/EcneProject/blob/master/src/gen_benchmark.jl)
