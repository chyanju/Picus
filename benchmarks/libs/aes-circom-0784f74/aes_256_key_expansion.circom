// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "helper_functions.circom";
include "aes_emulation_tables.circom";

template AES256KeyExpansion()
{
    signal input key[256];
    signal output w[1920];

    var rcon[10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36];

    var Nk = 8;
    var Nb = 4;
    var Nr = 14;
    var ks[60][32];
    var key_bits[32][8];

    var i, j, k;

    for(i=0; i<32; i++)
    {
        for(j=0; j<8; j++) key_bits[i][j] = key[i*8+j];
    }

    i = 0;
    while(i<Nk)
    {
        for(j=0; j<4; j++)
        {
            for(k=0; k<8; k++) ks[i][j*8+k] = key_bits[i*4+j][k];
        }
        i++;
    }

    component xor_1[60][32];
    component bits2num_1[60][4];
    component num2bits_1[60][5];
    component xor_2[60][8];


    while(i<(Nb*(Nr+1)))
    {
        var tmp[32];
        tmp = ks[i-1];

        if(i%Nk == 0)
        {
            bits2num_1[i][0] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][0].in[j] <== tmp[7-j];
            num2bits_1[i][0] = Num2Bits(8);
            num2bits_1[i][0].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][0].out);

            bits2num_1[i][1] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][1].in[j] <== tmp[7-j+8];
            num2bits_1[i][1] = Num2Bits(8);
            num2bits_1[i][1].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][1].out);

            bits2num_1[i][2] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][2].in[j] <== tmp[7-j+16];
            num2bits_1[i][2] = Num2Bits(8);
            num2bits_1[i][2].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][2].out);

            bits2num_1[i][3] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][3].in[j] <== tmp[7-j+24];
            num2bits_1[i][3] = Num2Bits(8);
            num2bits_1[i][3].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][3].out);

            for(j=0; j<8; j++) tmp[j+24] = num2bits_1[i][0].out[7-j];
            for(j=0; j<8; j++) tmp[j] = num2bits_1[i][1].out[7-j];
            for(j=0; j<8; j++) tmp[j+8] = num2bits_1[i][2].out[7-j];
            for(j=0; j<8; j++) tmp[j+16] = num2bits_1[i][3].out[7-j];

            num2bits_1[i][4] = Num2Bits(8);
            num2bits_1[i][4].in <== rcon[i/Nk-1];

            for(j=0; j<8; j++)
            {
                xor_2[i][j] = XOR();
                xor_2[i][j].a <== tmp[j];
                xor_2[i][j].b <== num2bits_1[i][4].out[7-j];

                tmp[j] = xor_2[i][j].out;
            }
        }
        else if(i%Nk == 4)
        {
            bits2num_1[i][0] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][0].in[j] <== tmp[7-j];
            num2bits_1[i][0] = Num2Bits(8);
            num2bits_1[i][0].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][0].out);

            bits2num_1[i][1] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][1].in[j] <== tmp[7-j+8];
            num2bits_1[i][1] = Num2Bits(8);
            num2bits_1[i][1].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][1].out);

            bits2num_1[i][2] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][2].in[j] <== tmp[7-j+16];
            num2bits_1[i][2] = Num2Bits(8);
            num2bits_1[i][2].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][2].out);

            bits2num_1[i][3] = Bits2Num(8);
            for(j=0; j<8; j++) bits2num_1[i][3].in[j] <== tmp[7-j+24];
            num2bits_1[i][3] = Num2Bits(8);
            num2bits_1[i][3].in <-- emulated_aesenc_rijndael_sbox(bits2num_1[i][3].out);

            for(j=0; j<8; j++) tmp[j] = num2bits_1[i][0].out[7-j];
            for(j=0; j<8; j++) tmp[j+8] = num2bits_1[i][1].out[7-j];
            for(j=0; j<8; j++) tmp[j+16] = num2bits_1[i][2].out[7-j];
            for(j=0; j<8; j++) tmp[j+24] = num2bits_1[i][3].out[7-j];
        }
        
        for(j=0; j<32; j++)
        {
            xor_1[i][j] = XOR();
            xor_1[i][j].a <== ks[i-Nk][j];
            xor_1[i][j].b <== tmp[j];

            ks[i][j] = xor_1[i][j].out;
        }
        i++;
    }

    for(i=0; i<60; i++)
    {
        for(j=0; j<32; j++) w[i*32+j] <== ks[i][j];
    }
}
