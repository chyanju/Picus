pragma circom 2.0.2;

include "../libs/circom-pairing/fp12.circom";

component main {public [in]} = Fp12Invert(4, 2, [1, 1]);
