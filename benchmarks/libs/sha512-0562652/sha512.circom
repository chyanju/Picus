pragma circom 2.0.0;

include "constants.circom";
include "sha512compression.circom";

template Sha512(nBits) {
    signal input in[nBits];
    signal output out[512];

    var i;
    var k;
    var nBlocks;
    var bitsLastBlock;


    nBlocks = ((nBits + 128)\1024)+1;

    signal paddedIn[nBlocks*1024];

    for (k=0; k<nBits; k++) {
        paddedIn[k] <== in[k];
    }
    paddedIn[nBits] <== 1;

    for (k=nBits+1; k<nBlocks*1024-128; k++) {
        paddedIn[k] <== 0;
    }

    for (k = 0; k< 128; k++) {
        paddedIn[nBlocks*1024 - k -1] <== (nBits >> k)&1;
    }

    component ha0 = H512(0);
    component hb0 = H512(1);
    component hc0 = H512(2);
    component hd0 = H512(3);
    component he0 = H512(4);
    component hf0 = H512(5);
    component hg0 = H512(6);
    component hh0 = H512(7);

    component sha512compression[nBlocks];

    for (i=0; i<nBlocks; i++) {

        sha512compression[i] = Sha512compression() ;

        if (i==0) {
            for (k=0; k<64; k++ ) {
                sha512compression[i].hin[0*64+k] <== ha0.out[k];
                sha512compression[i].hin[1*64+k] <== hb0.out[k];
                sha512compression[i].hin[2*64+k] <== hc0.out[k];
                sha512compression[i].hin[3*64+k] <== hd0.out[k];
                sha512compression[i].hin[4*64+k] <== he0.out[k];
                sha512compression[i].hin[5*64+k] <== hf0.out[k];
                sha512compression[i].hin[6*64+k] <== hg0.out[k];
                sha512compression[i].hin[7*64+k] <== hh0.out[k];
            }
        } else {
            for (k=0; k<64; k++ ) {
                sha512compression[i].hin[64*0+k] <== sha512compression[i-1].out[64*0+63-k];
                sha512compression[i].hin[64*1+k] <== sha512compression[i-1].out[64*1+63-k];
                sha512compression[i].hin[64*2+k] <== sha512compression[i-1].out[64*2+63-k];
                sha512compression[i].hin[64*3+k] <== sha512compression[i-1].out[64*3+63-k];
                sha512compression[i].hin[64*4+k] <== sha512compression[i-1].out[64*4+63-k];
                sha512compression[i].hin[64*5+k] <== sha512compression[i-1].out[64*5+63-k];
                sha512compression[i].hin[64*6+k] <== sha512compression[i-1].out[64*6+63-k];
                sha512compression[i].hin[64*7+k] <== sha512compression[i-1].out[64*7+63-k];
            }
        }

        for (k=0; k<1024; k++) {
            sha512compression[i].inp[k] <== paddedIn[i*1024+k];
        }
    }

    for (k=0; k<512; k++) {
        out[k] <== sha512compression[nBlocks-1].out[k];
    }

}
