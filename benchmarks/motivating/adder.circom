pragma circom 2.0.0;
include "../libs/circomlib-cff5ab6/bitify.circom";

template adder() {
    signal input b1;
    signal input b2;
    signal input carry;

    signal output v;
    signal output carry_out;

    b1*(b1-1) === 0;
    b2*(b2-1) === 0;
    carry*(carry-1) === 0;
    component n2b = Num2Bits(2);
    n2b.in <== b1 + b2 + carry;
    v <== n2b.out[0];
    carry_out <== n2b.out[1];
}

component main = adder();