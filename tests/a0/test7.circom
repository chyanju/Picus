pragma circom 2.0.0;

function helper(j,k) {
    var res = j+k;
    return res;
}

template Multiplier2(x,y) {
    signal input a;
    signal input b;
    signal output c;
    c <== helper(a,x) * helper(b,y);
 }

component main = Multiplier2(13,42);