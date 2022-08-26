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

include "sigma.circom";

template SigmaPlus512() {
    signal input in2[64];
    signal input in7[64];
    signal input in15[64];
    signal input in16[64];
    signal output out[64];
    var k;

    component sigma1 = SmallSigma512(19,61,6);
    component sigma0 = SmallSigma512(1, 8, 7);
    for (k=0; k<64; k++) {
        sigma1.in[k] <== in2[k];
        sigma0.in[k] <== in15[k];
    }

    component sum = BinSum(64, 4);
    for (k=0; k<64; k++) {
        sum.in[0][k] <== sigma1.out[k];
        sum.in[1][k] <== in7[k];
        sum.in[2][k] <== sigma0.out[k];
        sum.in[3][k] <== in16[k];
    }

    for (k=0; k<64; k++) {
        out[k] <== sum.out[k];
    }
}
