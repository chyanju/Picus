pragma circom 2.0.3;

include "matElemSum.circom";

// trace of a square matrix
template trace (m) {
    signal input a[m][m];
    signal output out;

    component comp = matElemSum(1,m);
    
    for (var i=0; i < m; i++) {
        comp.a[0][i] <== a[i][i];
    }

    out <== comp.out;
}