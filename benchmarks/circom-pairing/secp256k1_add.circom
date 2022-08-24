pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/curve.circom";

component main {public [a, b]} = EllipticCurveAddUnequal(52, 5, [4503595332402223, 4503599627370495, 4503599627370495, 4503599627370495, 281474976710655]);
