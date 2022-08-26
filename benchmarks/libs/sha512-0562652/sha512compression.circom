/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

include "constants.circom";
include "t1.circom";
include "t2.circom";
include "sigmaplus.circom";


template Sha512compression() {
    signal input hin[512];
    signal input inp[1024];
    signal output out[512];
    signal a[81][64];
    signal b[81][64];
    signal c[81][64];
    signal d[81][64];
    signal e[81][64];
    signal f[81][64];
    signal g[81][64];
    signal h[81][64];
    signal w[80][64];

    var i;

    component sigmaPlus[64];
    for (i=0; i<64; i++) sigmaPlus[i] = SigmaPlus512();

    component ct_k[80];
    for (i=0; i<80; i++) ct_k[i] = K512(i);

    component t1[80];
    for (i=0; i<80; i++) t1[i] = T1_512();

    component t2[80];
    for (i=0; i<80; i++) t2[i] = T2_512();

    component suma[80];
    for (i=0; i<80; i++) suma[i] = BinSum(64, 2);

    component sume[80];
    for (i=0; i<80; i++) sume[i] = BinSum(64, 2);

    component fsum[8];
    for (i=0; i<8; i++) fsum[i] = BinSum(64, 2);

    var k;
    var t;

    for (t=0; t<80; t++) {
        if (t<16) {
            for (k=0; k<64; k++) {
                w[t][k] <== inp[t*64+63-k];
            }
        } else {
            for (k=0; k<64; k++) {
                sigmaPlus[t-16].in2[k] <== w[t-2][k];
                sigmaPlus[t-16].in7[k] <== w[t-7][k];
                sigmaPlus[t-16].in15[k] <== w[t-15][k];
                sigmaPlus[t-16].in16[k] <== w[t-16][k];
            }

            for (k=0; k<64; k++) {
                w[t][k] <== sigmaPlus[t-16].out[k];
            }
        }
    }

    for (k=0; k<64; k++ ) {
        a[0][k] <== hin[k];
        b[0][k] <== hin[64*1 + k];
        c[0][k] <== hin[64*2 + k];
        d[0][k] <== hin[64*3 + k];
        e[0][k] <== hin[64*4 + k];
        f[0][k] <== hin[64*5 + k];
        g[0][k] <== hin[64*6 + k];
        h[0][k] <== hin[64*7 + k];
    }

    for (t = 0; t<80; t++) {
        for (k=0; k<64; k++) {
            t1[t].h[k] <== h[t][k];
            t1[t].e[k] <== e[t][k];
            t1[t].f[k] <== f[t][k];
            t1[t].g[k] <== g[t][k];
            t1[t].k[k] <== ct_k[t].out[k];
            t1[t].w[k] <== w[t][k];

            t2[t].a[k] <== a[t][k];
            t2[t].b[k] <== b[t][k];
            t2[t].c[k] <== c[t][k];
        }

        for (k=0; k<64; k++) {
            sume[t].in[0][k] <== d[t][k];
            sume[t].in[1][k] <== t1[t].out[k];

            suma[t].in[0][k] <== t1[t].out[k];
            suma[t].in[1][k] <== t2[t].out[k];
        }

        for (k=0; k<64; k++) {
            h[t+1][k] <== g[t][k];
            g[t+1][k] <== f[t][k];
            f[t+1][k] <== e[t][k];
            e[t+1][k] <== sume[t].out[k];
            d[t+1][k] <== c[t][k];
            c[t+1][k] <== b[t][k];
            b[t+1][k] <== a[t][k];
            a[t+1][k] <== suma[t].out[k];
        }
    }

    for (k=0; k<64; k++) {
        fsum[0].in[0][k] <==  hin[64*0+k];
        fsum[0].in[1][k] <==  a[80][k];
        fsum[1].in[0][k] <==  hin[64*1+k];
        fsum[1].in[1][k] <==  b[80][k];
        fsum[2].in[0][k] <==  hin[64*2+k];
        fsum[2].in[1][k] <==  c[80][k];
        fsum[3].in[0][k] <==  hin[64*3+k];
        fsum[3].in[1][k] <==  d[80][k];
        fsum[4].in[0][k] <==  hin[64*4+k];
        fsum[4].in[1][k] <==  e[80][k];
        fsum[5].in[0][k] <==  hin[64*5+k];
        fsum[5].in[1][k] <==  f[80][k];
        fsum[6].in[0][k] <==  hin[64*6+k];
        fsum[6].in[1][k] <==  g[80][k];
        fsum[7].in[0][k] <==  hin[64*7+k];
        fsum[7].in[1][k] <==  h[80][k];
    }

    for (k=0; k<64; k++) {
        out[63-k]     <== fsum[0].out[k];
        out[64+63-k]  <== fsum[1].out[k];
        out[128+63-k]  <== fsum[2].out[k];
        out[192+63-k]  <== fsum[3].out[k];
        out[256+63-k] <== fsum[4].out[k];
        out[320+63-k] <== fsum[5].out[k];
        out[384+63-k] <== fsum[6].out[k];
        out[448+63-k] <== fsum[7].out[k];
    }
}
