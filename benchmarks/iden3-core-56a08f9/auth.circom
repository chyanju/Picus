pragma circom 2.0.0;

include "../libs/iden3-core-56a08f9/authentication.circom";

component main {public [userID,challenge,userState]} = VerifyAuthentication(32);