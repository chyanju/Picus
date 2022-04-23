pragma circom 2.0.0;

template Multiplier2(x,y,n) {
    signal input a;
    signal input b;
    signal output c;
    if (n>0) {
        c <== (a+x)*(b+y);
    } else {
        c <== a*b + x*y;
    }
 }

component main = Multiplier2(13,42,-5);