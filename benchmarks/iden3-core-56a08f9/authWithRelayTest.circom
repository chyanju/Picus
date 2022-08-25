pragma circom 2.0.0;

include "../libs/iden3-core-56a08f9/authenticationWithRelay.circom";

component main {public [challenge,userState]} = VerifyAuthenticationWithRelay(32, 4);
