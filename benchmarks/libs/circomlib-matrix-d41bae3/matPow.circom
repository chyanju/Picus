pragma circom 2.0.3;

include "matMul.circom";

// matrix raised to a power
template matPow (n,p) {
    signal input a[n][n];
    signal output out[n][n];

    assert(p > 0);

    component comp[p];

    comp[0] = matMul(n,n,n);

    for (var i=0; i < n; i++){
        for (var j=0; j < n; j++) {
            comp[0].a[i][j] <== a[i][j];
            if (i==j) {
                comp[0].b[i][j] <== 1;
            } else {
                comp[0].b[i][j] <== 0;
            }
        }
    }

    for (var k=1; k<p; k++) {
        comp[k] = matMul(n,n,n);
        for (var i=0; i < n; i++) {
            for (var j=0; j < n; j++) {
                comp[k].a[i][j] <== comp[k-1].out[i][j];
                comp[k].b[i][j] <== a[i][j];
            }
        }
    }

    for (var i=0; i < n; i++){
        for (var j=0; j < n; j++) {
            out[i][j] <== comp[p-1].out[i][j];
        }
    }
}