pragma circom 2.0.2;

include "../libs/circom-pairing/fp2.circom";

component main {public [a, b]} = Fp2Add(2, 2, [3, 2]);
