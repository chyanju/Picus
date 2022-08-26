pragma circom 2.0.0;

include "../libs/ed25519-099d19c-fixed/chunkedadd.circom";

component main = ChunkedAdd(4,4,51);