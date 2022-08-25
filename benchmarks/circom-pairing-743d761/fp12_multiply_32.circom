pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/fp12.circom";

component main {public [a, b]} = Fp12Multiply(3, 2, [3, 2]);
