pragma circom 2.0.2;

include "../libs/circom-ecdsa-d87eb70/ecdsa.circom";

component main {public [r, s, msghash, pubkey]} = ECDSAVerifyNoPubkeyCheck(64, 4);
