// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "helper_functions.circom";

template Mul()
{
    signal input src1[64];
    signal input src2[64];
    signal output out[128];

    var i, j, k;

    var dst_bytes[2][64];
    var src1_bytes[64], src2_bytes[64];

    for(i=0; i<8; i++)
    {
        for(j=0; j<8; j++)
        {
            src1_bytes[i*8+j] = src1[i*8+7-j];
            src2_bytes[i*8+j] = src2[i*8+7-j];
        }
    }

    component xor_1[64][2][64];

    var const_bytes[64];
    for(i=0; i<64; i++)
    {
        dst_bytes[0][i] = 0;
        dst_bytes[1][i] = 0;
        const_bytes[i] = 0;
    }
    const_bytes[63] = 1;

    for(i=0; i<64; i++)
    {
        var src1_bytes_t[64];
        for(j=0; j<64; j++)
        {
            src1_bytes_t[j] = src1_bytes[j] * src2_bytes[i];
            xor_1[i][0][j] = XOR();
            
            xor_1[i][0][j].a <== dst_bytes[1][j];
            xor_1[i][0][j].b <== src1_bytes_t[j];

            dst_bytes[1][j] = xor_1[i][0][j].out;
        }
        for(j=0; j<63; j++)
        {
            dst_bytes[0][j] = dst_bytes[0][j+1];
        }
        dst_bytes[0][63] = 0;

        var const_bytes_t[64];
        for(j=0; j<64; j++)
        {
            const_bytes_t[j] = const_bytes[j] * dst_bytes[1][0];
            xor_1[i][1][j] = XOR();

            xor_1[i][1][j].a <== dst_bytes[0][j];
            xor_1[i][1][j].b <== const_bytes_t[j];

            dst_bytes[0][j] = xor_1[i][1][j].out;
        }
        for(j=0; j<63; j++)
        {
            dst_bytes[1][j] = dst_bytes[1][j+1];
        }
        dst_bytes[1][63] = 0;
    }

    for(i=0; i<2; i++)
    {
        for(j=0; j<8; j++)
        {
            for(k=0; k<8; k++) out[i*64+j*8+k] <== dst_bytes[i][j*8+7-k];
        }
    }

}