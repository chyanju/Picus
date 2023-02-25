pragma circom 2.0.2;

include "../libs/circom-pairing-743d761/bigint.circom";

// k>=2, n<=251
component main = BigMultShortLong(126,16,0);