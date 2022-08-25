pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/pairing.circom";

component main {public [P]} = Fp12MultiplyWithLineUnequal(3, 2, 2, 3, [3, 2]);
