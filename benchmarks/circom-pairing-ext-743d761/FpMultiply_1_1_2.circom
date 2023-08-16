pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/fp.circom";

component main {public [a,b]} = FpMultiply(4, 3, [1, 1, 1]);