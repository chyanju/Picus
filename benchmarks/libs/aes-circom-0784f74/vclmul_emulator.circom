// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "mul.circom";

template VCLMULEmulator(imm) {
    signal input src1[2][64];
    signal input src2[2][64];
    signal output destination[2][64];

    component mul = Mul();

    var i, j;

    if(imm == 0){
        for(i=0; i<64; i++)
        {
            mul.src1[i] <== src1[0][i];
            mul.src2[i] <== src2[0][i];
        }
    }
    else if(imm == 1){
        for(i=0; i<64; i++)
        {
            mul.src1[i] <== src1[1][i];
            mul.src2[i] <== src2[0][i];
        }
    }
    else if(imm == 2){
        for(i=0; i<64; i++)
        {
            mul.src1[i] <== src1[0][i];
            mul.src2[i] <== src2[1][i];
        }
    }
    else if(imm == 3){
        for(i=0; i<64; i++)
        {
            mul.src1[i] <== src1[1][i];
            mul.src2[i] <== src2[1][i];
        }
    }

    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) destination[i][j] <== mul.out[i*64+j];
    }
}