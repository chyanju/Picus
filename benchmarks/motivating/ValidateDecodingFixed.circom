pragma circom 2.0.0;
include "../libs/circomlib-cff5ab6/comparators.circom";

template ValidateDecoding(w) {
    signal input inp;
    signal input out[w];
    signal output success;
    var lc = 0;

    for (var i = 0; i < w; i ++) {
        out[i] * (inp - i) === 0;
        lc = lc + out[i];
    }

    component checkZero = IsZero();
    checkZero.in <== lc - 1;
    success <== checkZero.out;
}

component main = ValidateDecoding(2);