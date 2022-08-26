// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "vclmul_emulator.circom";
include "helper_functions.circom";

template GFMULInt()
{
    signal input a[2][64];
    signal input b[2][64];
    signal output res[2][64];

    var tmp[5][2][64];
    var XMMMASK[2] = [0x1, 0xc200000000000000];

        var i, j, k;

    component num2bits_1[2];
    var XMMMASK_bits[2][64];
    for(i=0; i<2; i++)
    {
        num2bits_1[i] = Num2Bits(64);
        num2bits_1[i].in <== XMMMASK[i];
        for(j=0; j<8; j++)
        {
            for(k=0; k<8; k++) XMMMASK_bits[i][j*8+k] = num2bits_1[i].out[j*8+7-k];
        }
    }

    component vclmul_emulator_1[4];
    
    for(i=0; i<4; i++)
    {
        vclmul_emulator_1[i] = VCLMULEmulator(i);
        for(j=0; j<2; j++)
        {
            for(k=0; k<64; k++)
            {
                vclmul_emulator_1[i].src1[j][k] <== a[j][k];
                vclmul_emulator_1[i].src2[j][k] <== b[j][k];
            }
        }

        tmp[i+1] = vclmul_emulator_1[i].destination;
    }

    component xor_1[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_1[i][j] = XOR();
            xor_1[i][j].a <== tmp[2][i][j];
            xor_1[i][j].b <== tmp[3][i][j];

            tmp[2][i][j] = xor_1[i][j].out;
        }
    }

    for(i=0; i<64; i++) tmp[3][0][i] = 0;

    for(i=0; i<64; i++) tmp[3][1][i] = tmp[2][0][i];

    for(i=0; i<64; i++) tmp[2][0][i] = tmp[2][1][i];

    for(i=0; i<64; i++) tmp[2][1][i] = 0;

    component xor_2[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_2[i][j] = XOR();
            xor_2[i][j].a <== tmp[1][i][j];
            xor_2[i][j].b <== tmp[3][i][j];

            tmp[1][i][j] = xor_2[i][j].out;
        }
    }

    component xor_3[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_3[i][j] = XOR();
            xor_3[i][j].a <== tmp[4][i][j];
            xor_3[i][j].b <== tmp[2][i][j];

            tmp[4][i][j] = xor_3[i][j].out;
        }
    }

    component vclmul_emulator_2 = VCLMULEmulator(1);
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            vclmul_emulator_2.src1[i][j] <== XMMMASK_bits[i][j];
            vclmul_emulator_2.src2[i][j] <== tmp[1][i][j];
        }
    }

    tmp[2] = vclmul_emulator_2.destination;

    for(i=0; i<64; i++)
    {
        tmp[3][0][i] = tmp[1][1][i];
        tmp[3][1][i] = tmp[1][0][i];
    }

    component xor_4[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_4[i][j] = XOR();
            xor_4[i][j].a <== tmp[2][i][j];
            xor_4[i][j].b <== tmp[3][i][j];

            tmp[1][i][j] = xor_4[i][j].out;
        }
    }

    component vclmul_emulator_3 = VCLMULEmulator(1);
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            vclmul_emulator_3.src1[i][j] <== XMMMASK_bits[i][j];
            vclmul_emulator_3.src2[i][j] <== tmp[1][i][j];
        }
    }

    tmp[2] = vclmul_emulator_3.destination;

    for(i=0; i<64; i++)
    {
        tmp[3][0][i] = tmp[1][1][i];
        tmp[3][1][i] = tmp[1][0][i];
    }

    component xor_5[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_5[i][j] = XOR();
            xor_5[i][j].a <== tmp[2][i][j];
            xor_5[i][j].b <== tmp[3][i][j];

            tmp[1][i][j] = xor_5[i][j].out;
        }
    }

    component xor_6[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_6[i][j] = XOR();
            xor_6[i][j].a <== tmp[1][i][j];
            xor_6[i][j].b <== tmp[4][i][j];

            res[i][j] <== xor_6[i][j].out;
        }
    }
}