pragma circom 2.0.3;

// outer product
template outer (m,n) {
    signal input a[m];
    signal input b[n];
    signal output out[m][n];
    
    for (var i=0; i < m; i++) {
        for (var j=0; j < n; j++) {
            out[i][j] <== a[i]*b[j];
        }
    }
}