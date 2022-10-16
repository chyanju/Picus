pragma circom 2.0.0;

// template BabyAdd() {
//     signal input x1;
//     signal input y1;
//     signal input x2;
//     signal input y2;
//     signal output xout;
//     signal output yout;

//     signal beta;
//     signal gamma;
//     signal delta;
//     signal tau;

//     var a = 168700;
//     var d = 168696;

//     beta <== x1*y2;
//     gamma <== y1*x2;
//     delta <== (-a*x1+y1)*(x2 + y2);
//     tau <== beta * gamma;

//     xout <-- (beta + gamma) / (1+ d*tau);
//     (1+ d*tau) * xout === (beta + gamma);

//     yout <-- (delta + a*beta - gamma) / (1-d*tau);
//     (1-d*tau)*yout === (delta + a*beta - gamma);
// }

// component main = BabyAdd();

template BabyTest() {
    signal input x;
    signal input y;
    signal input z;
    signal output out;

    signal tau;
    tau <== x * y;
    out <-- z / tau;
    tau * out === z;
}

component main = BabyTest();