pragma circom 2.0.3;

include "power.circom";

// matrix raised to a power by element
template matElemPow (m,n,p) {
    signal input a[m][n];
    signal output out[m][n];

    assert(p > 0);
    
    component pow[m][n];
    for (var i=0; i < m; i++) {
        for (var j=0; j < n; j++) {
            pow[i][j] = power(p);
            pow[i][j].a <== a[i][j];
            out[i][j] <== pow[i][j].out;
        }
    }
}