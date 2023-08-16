pragma circom 2.0.0;


template ValidateDecoding(w) {
    signal input x;
    signal input arr[w];
    signal output success;
    var lc = 0;

    for (var i = 0; i < w; i ++) {
        arr[i] * (x - i) === 0;
        lc = lc + arr[i];
    }
    success <-- (lc == 1) ? 1 : 0;
    success * (success - 1) === 0;
}

component main = ValidateDecoding(2);