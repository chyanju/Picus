pragma circom 2.0.0;

template Multiplier2(x,y,n) {
    signal input a;
    signal input b;
    signal output c;
    c <== n==0 ? x*y + a*b : x*x + y*y + a*b;
 }

component main = Multiplier2(13,42,1);