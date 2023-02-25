pragma circom 2.0.2;

// include "../libs/circom-pairing-743d761/bigint.circom";

template Split(n, m) {
    assert(n <= 126);
    signal input in;
    signal output small;
    signal output big;

    small <-- in % (1 << n);
    big <-- in \ (1 << n);

    in === small + big * (1 << n);
}

component main = Split(8,254);