pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/fp12.circom";

component main {public [in]} = Fp12Invert(4, 2, [1, 1]);
