pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/final_exp.circom";

component main {public [in]} = Fp12CyclotomicExp(3, 2, 5, [3, 2]);
