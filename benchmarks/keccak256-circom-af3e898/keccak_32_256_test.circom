pragma circom 2.0.0;

include "../libs/keccak256-circom-af3e898/keccak.circom";

component main = Keccak(4*8, 32*8);
