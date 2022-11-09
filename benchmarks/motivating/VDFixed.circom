pragma circom 2.0.0;
include "../libs/circomlib-cff5ab6/gates.circom";
include "../libs/circomlib-cff5ab6/comparators.circom";

template Decoder(w) {
    signal input inp;
    signal output out[w];
    signal output success;
    var lc=0;
		
    component checkZero[w];
    for (var i=0; i<w; i++) {
        checkZero[i] = IsZero();
        checkZero[i].in <== inp - i;
        checkZero[i].out ==> out[i];
        lc = lc + out[i];
    }
    lc ==> success;
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