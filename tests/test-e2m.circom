include "../benchmarks/libs/circomlib-cff5ab6/comparators.circom";
template Edwards2Montgomery() {
    signal input in[2];
    signal output out[2];
    component checkZero0 = IsZero();
    component checkZero1 = IsZero();
    
    checkZero0.in <== in[0];
    checkZero0.out === 0;

    checkZero1.in <== 1 - in[1];
    checkZero1.out === 0;
    
    out[0] <-- (1 + in[1]) / (1 - in[1]);
    out[1] <-- out[0] / in[0];
    out[0] * (1-in[1]) === (1 + in[1]);
    out[1] * in[0] === out[0];
}

component main = Edwards2Montgomery();