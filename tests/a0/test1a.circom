pragma circom 2.0.0;

template Multiplier2(x,y) {
    signal input a;
    signal input b;
    signal output c;
    c <== (a+x)*(b+y);
 }

component main = Multiplier2(14,42);