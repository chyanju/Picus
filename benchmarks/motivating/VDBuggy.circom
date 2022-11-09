pragma circom 2.0.0;
include "../libs/circomlib-cff5ab6/gates.circom";
include "../libs/circomlib-cff5ab6/comparators.circom";

template Decoder(w) {
    signal input inp;
    signal output out[w];
    signal output success;
    var lc=0;

    for (var i=0; i<w; i++) {
        out[i] <-- (inp == i) ? 1 : 0;
        out[i] * (inp-i) === 0;
        lc = lc + out[i];
    }

    lc ==> success;
    success * (success -1) === 0;
}

template ValidateDecoding(w) {
    signal input x;
    signal input arr[w];
    signal output success;

    component multiAnd = MultiAND(w);
    component decoder = Decoder(w);
    component checkEq[w];
    decoder.inp <== x;
    for (var i=0; i<w; i++) {
        checkEq[i] = IsEqual();
        checkEq[i].in[0] <== arr[i];
        checkEq[i].in[1] <== decoder.out[i];
        multiAnd.in[i] <== checkEq[i].out;
    }
    success <== multiAnd.out;
}

component main = ValidateDecoding(2);