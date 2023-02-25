include "../benchmarks/libs/circomlib-cff5ab6/comparators.circom";
template MontgomeryAdd() {
    signal input in1[2];
    signal input in2[2];
    signal output out[2];

    var a = 168700;
    var d = 168696;

    var A = (2 * (a + d)) / (a - d);
    var B = 4 / (a - d);

    component checkZero = IsZero();
    checkZero.in <== in2[0] - in1[0];
    checkZero.out === 0;

    signal lamda;

    lamda <-- (in2[1] - in1[1]) / (in2[0] - in1[0]);
    lamda * (in2[0] - in1[0]) === (in2[1] - in1[1]);

    out[0] <== B*lamda*lamda - A - in1[0] -in2[0];
    out[1] <== lamda * (in1[0] - out[0]) - in1[1];
}

component main = MontgomeryAdd();