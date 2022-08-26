// Copyright © 2022, Electron Labs
pragma circom 2.0.0;

include "aes_emulation_tables.circom";

template EmulatedAesencRowShifting()
{
    signal input in[16];
    signal output out[16];
    
    var byte_order[16];
    byte_order[0]  = 0;
    byte_order[1]  = 5;
    byte_order[2]  = 10;
    byte_order[3]  = 15;
    byte_order[4]  = 4;
    byte_order[5]  = 9;
    byte_order[6]  = 14;
    byte_order[7]  = 3;
    byte_order[8]  = 8;
    byte_order[9]  = 13;
    byte_order[10] = 2;
    byte_order[11] = 7;
    byte_order[12] = 12;
    byte_order[13] = 1;
    byte_order[14] = 6;
    byte_order[15] = 11;

    for(var i=0; i<16; i++) out[i] <== in[byte_order[i]];
}

template EmulatedAesencSubstituteBytes()
{
    signal input in[16];
    signal output out[16];

    for(var i=0; i<16; i++) out[i] <-- emulated_aesenc_rijndael_sbox(in[i]);
    
}
