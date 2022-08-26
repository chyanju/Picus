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
include "ch.circom";

template T1_512() {
    signal input h[64];
    signal input e[64];
    signal input f[64];
    signal input g[64];
    signal input k[64];
    signal input w[64];
    signal output out[64];

    var ki;

    component ch = Ch_t512(64);
    component bigsigma1 = BigSigma512(14, 18, 41);

    for (ki=0; ki<64; ki++) {
        bigsigma1.in[ki] <== e[ki];
        ch.a[ki] <== e[ki];
        ch.b[ki] <== f[ki];
        ch.c[ki] <== g[ki];
    }

    component sum = BinSum(64, 5);
    for (ki=0; ki<64; ki++) {
        sum.in[0][ki] <== h[ki];
        sum.in[1][ki] <== bigsigma1.out[ki];
        sum.in[2][ki] <== ch.out[ki];
        sum.in[3][ki] <== k[ki];
        sum.in[4][ki] <== w[ki];
    }

    for (ki=0; ki<64; ki++) {
        out[ki] <== sum.out[ki];
    }
}
