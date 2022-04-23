pragma circom 2.0.0;

template Multiplier2(x,y) {
    signal input a;
    signal input b;
    signal output c;
    assert(x>=0);
    assert(y>=0);
    c <== x*y + a*b;
 }

component main = Multiplier2(13,42);