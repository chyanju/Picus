pragma circom 2.0.0;

include "../libs/iden3-core-56a08f9/stateTransition.circom";

component main {public [userID,oldUserState,newUserState,isOldStateGenesis]} = StateTransition(32);
