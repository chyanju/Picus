# Picus
Equivalence Verification for R1CS

## Commands

```bash
circom ./test0.circom --r1cs --wasm --sym --c
```

## Notes

- The current R1CS parser is a stricter version that only allows 3 sections of type 1, 2 and 3 only. For the parser that complies with the currently very loose spec of R1CS ([https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)), please see `r1cs-ext.rkt`. To have better control of the prototype, the stricter version is used instead.

## Resources

- R1CS Binary Format: [https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)
- GF example meaning: [https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7](https://discourse.julialang.org/t/new-type-definition-galois-field-in-julia-1-x/17123/7)
- 
