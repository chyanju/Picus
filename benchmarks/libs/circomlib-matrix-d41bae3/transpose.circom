pragma circom 2.0.3;

// matrix transpose
template transpose (m,n) {
    signal input a[m][n];
    signal output out[n][m];
    
    for (var i=0; i < m; i++) {
        for (var j=0; j < n; j++) {
            out[j][i] <== a[i][j];
        }
    }
}