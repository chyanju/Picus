pragma circom 2.0.0;

include "../libs/iden3-core-56a08f9/utils/claimUtils.circom";

component main{public[claim]} = getClaimSubjectOtherIden();
