pragma circom 2.0.3;

// compute power of a number
template power (p) {
    signal input a;
    signal output out;

    assert(p > 0);

    signal prod[p];

    prod[0] <== a;
    
    for (var i=1; i < p; i++) {
        prod[i] <== prod[i-1] * a;
    }

    out <== prod[p-1];
}