// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "aes_256_key_expansion.circom";
include "aes_256_encrypt.circom";
include "aes_256_ctr.circom";
include "polyval.circom";
include "helper_functions.circom";
include "../circomlib-cff5ab6/mux1.circom";

template GCM_SIV_DEC_2_Keys(n_bits_aad, n_bits_msg)
{
    var aad_len = n_bits_aad/8;
    var msg_len = n_bits_msg/8;
    assert(aad_len%16 == 0);
    assert(msg_len%16 == 0);
    signal input K1[256];
    signal input N[128];
    signal input AAD[n_bits_aad];
    signal input CT[(msg_len+16)*8];

    signal output MSG[n_bits_msg];
    signal output success;

    var i, j, k;

    var MSG_t[msg_len*8];
    var CT_msg[msg_len*8];
    for(i=0; i<msg_len*8; i++) CT_msg[i] = CT[i];
    var TAG[128];
    for(i=0; i<128; i++) TAG[i] = CT[msg_len*8+i];
    var ks[1920];
    var _N[128];
    var _T[768];
    var Record_Hash_Key[128];
    var Record_Enc_Key[256];
    var T[2][64];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) T[i][j] = 0;
    }
    var new_TAG[128];
    var CTR[128];
    var LENBLK_bits[2][64];

    component num2bits_1[2];
    num2bits_1[0] = Num2Bits(64);
    num2bits_1[0].in <== aad_len*8;
    num2bits_1[1] = Num2Bits(64);
    num2bits_1[1].in <== msg_len*8;

    for(i=0; i<2; i++)
    {
        for(j=0; j<8; j++)
        {
            for(k=0; k<8; k++) LENBLK_bits[i][j*8+k] = num2bits_1[i].out[j*8+7-k];
        }
    }

    for(i=0; i<128; i++) CTR[i] = TAG[i];
    CTR[15*8] = 1;

    component key_expansion_1 = AES256KeyExpansion();
    for(i=0; i<256; i++) key_expansion_1.key[i] <== K1[i];
    ks = key_expansion_1.w;

    for(i=0; i<3*32; i++)
    {
        _N[i+32] = N[i];
    }

    component num2bits_2[6];
    component aes_256_encrypt_1[6];

    for(i=0; i<6; i++) 
    {
        aes_256_encrypt_1[i] = AES256Encrypt();
        num2bits_2[i] = Num2Bits(32);
        num2bits_2[i].in <== i;
        for(j=0; j<4; j++)
        {
            for(k=0; k<8; k++) _N[j*8+k] = num2bits_2[i].out[j*8+7-k];
        }
        var _T_tmp[128];

        for(j=0; j<128; j++) aes_256_encrypt_1[i].in[j] <== _N[j];
        for(j=0; j<1920; j++) aes_256_encrypt_1[i].ks[j] <== ks[j];
        _T_tmp = aes_256_encrypt_1[i].out;
        for(j=0; j<128; j++) _T[i*128+j] = _T_tmp[j];
    }

    for(i=0; i<64; i++) Record_Hash_Key[i] = _T[i];
    for(i=0; i<64; i++) Record_Hash_Key[i+64] = _T[64*2+i];
    for(i=0; i<64; i++) Record_Enc_Key[i] = _T[64*4+i];
    for(i=0; i<64; i++) Record_Enc_Key[i+64] = _T[64*6+i];
    for(i=0; i<64; i++) Record_Enc_Key[i+64*2] = _T[64*8+i];
    for(i=0; i<64; i++) Record_Enc_Key[i+64*3] = _T[64*10+i];

    component key_expansion_2 = AES256KeyExpansion();
    for(i=0; i<256; i++) key_expansion_2.key[i] <== Record_Enc_Key[i];
    ks = key_expansion_2.w;

    component aes_256_ctr = AES256CTR(msg_len*8);
    for(i=0; i<msg_len*8; i++) aes_256_ctr.in[i] <== CT_msg[i];
    for(i=0; i<128; i++) aes_256_ctr.ctr[i] <== CTR[i];
    for(i=0; i<1920; i++) aes_256_ctr.ks[i] <== ks[i];
    MSG_t = aes_256_ctr.out;

    component polyval_1 = POLYVAL(n_bits_aad);
    if(aad_len != 0)
    {
        for(i=0; i<n_bits_aad; i++) polyval_1.in[i] <== AAD[i];
        for(i=0; i<128; i++) polyval_1.H[i] <== Record_Hash_Key[i];
        for(i=0; i<2; i++)
        {
            for(j=0; j<64; j++) polyval_1.T[i][j] <== T[i][j];
        }
        T = polyval_1.result;
    }

    component polyval_2 = POLYVAL(n_bits_msg);
    for(i=0; i<n_bits_msg; i++) polyval_2.in[i] <== MSG_t[i];
    for(i=0; i<128; i++) polyval_2.H[i] <== Record_Hash_Key[i];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) polyval_2.T[i][j] <== T[i][j];
    }
    T = polyval_2.result;

    component polyval_3 = POLYVAL(128);
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) polyval_3.in[i*64+j] <== LENBLK_bits[i][j];
    }
    for(i=0; i<128; i++) polyval_3.H[i] <== Record_Hash_Key[i];
    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) polyval_3.T[i][j] <== T[i][j];
    }
    T = polyval_3.result;

    component xor_1[2][64];

    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++)
        {
            xor_1[i][j] = XOR();
            xor_1[i][j].a <== T[i][j];
            xor_1[i][j].b <== N[i*64+j];

            T[i][j] = xor_1[i][j].out;
        }
    }

    for(i=0; i<2; i++)
    {
        for(j=0; j<64; j++) new_TAG[i*64+j] = T[i][j];
    }

    new_TAG[15*8] = 0;

    component aes_256_encrypt_2 = AES256Encrypt();
    for(i=0; i<128; i++) aes_256_encrypt_2.in[i] <== new_TAG[i];
    for(i=0; i<1920; i++) aes_256_encrypt_2.ks[i] <== ks[i];
    new_TAG = aes_256_encrypt_2.out;

    component is_equal_1[128];
    for(i=0; i<128; i++) is_equal_1[i] = IsEqual();

    for(i=0; i<128; i++)
    {
        is_equal_1[i].in[0] <== new_TAG[i];
        is_equal_1[i].in[1] <== TAG[i];
    }

    component mux_1 = Mux1();
    mux_1.c[0] <== 0;
    mux_1.c[1] <== 1;
    component multi_and = MultiAND(128);
    for(i=0; i<128; i++) multi_and.in[i] <== is_equal_1[i].out;
    mux_1.s <== multi_and.out;

    success <== mux_1.out;

    component mux_2[msg_len*8];
    for(i=0; i<msg_len*8; i++) mux_2[i] = Mux1();

    for(i=0; i<msg_len*8; i++)
    {
        mux_2[i].c[0] <== CT_msg[i];
        mux_2[i].c[1] <== MSG_t[i];
        mux_2[i].s <== multi_and.out;

        MSG[i] <== mux_2[i].out;
    }
}