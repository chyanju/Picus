include "../../libs/circomlib-cff5ab6/smt/smtprocessor.circom";
include "../../libs/circomlib-cff5ab6/eddsaposeidon.circom";
include "../../libs/circomlib-cff5ab6/gates.circom";
include "../../libs/circomlib-cff5ab6/mux1.circom";

include "./decode-tx.circom";
include "./rollup-tx.circom";
include "./hash-inputs.circom";
include "./fee-tx.circom";

/**
 * Decodes and process all rollup transactions and pay accumulated fees
 * @param nTx - absolute maximum of L1 or L2 transactions
 * @param nLevels - merkle tree depth
 * @param maxL1Tx - absolute maximum of L1 transaction
 * @param maxFeeTx - absolute maximum of fee transactions
 */
template RollupMain(nTx, nLevels, maxL1Tx, maxFeeTx){
    // Unique public signal
    signal output hashGlobalInputs;

    // private signals taking part of the hash-input
    signal input oldLastIdx;
    signal input oldStateRoot;
    signal input globalChainID;
    signal input feeIdxs[maxFeeTx];

    // accumulate fees
    signal input feePlanTokens[maxFeeTx];

    // Intermediary States to parallelize witness computation
    // decode-tx
    signal input imOnChain[nTx-1];
    signal input imOutIdx[nTx-1];
    // rollup-tx
    signal input imStateRoot[nTx-1];
    signal input imExitRoot[nTx-1];
    signal input imAccFeeOut[nTx-1][maxFeeTx];
    // fee-tx
    signal input imStateRootFee[maxFeeTx - 1];
    signal input imInitStateRootFee;
    signal input imFinalAccFee[maxFeeTx];

    // transaction L1-L2
    signal input txCompressedData[nTx];
    signal input txCompressedDataV2[nTx];

    signal input fromIdx[nTx];
    signal input auxFromIdx[nTx];

    signal input toIdx[nTx];
    signal input auxToIdx[nTx];
    signal input toBjjAy[nTx];
    signal input toEthAddr[nTx];

    signal input onChain[nTx];
    signal input newAccount[nTx];
    signal input rqOffset[nTx];

    // transaction L2 request data
    signal input rqTxCompressedDataV2[nTx];
    signal input rqToEthAddr[nTx];
    signal input rqToBjjAy[nTx];

    // transaction L2 signature
    signal input s[nTx];
    signal input r8x[nTx];
    signal input r8y[nTx];

    // transaction L1
    signal input loadAmountF[nTx];
    signal input fromEthAddr[nTx];
    signal input fromBjjCompressed[nTx][256];

    // State 1
    signal input tokenID1[nTx];
    signal input nonce1[nTx];
    signal input sign1[nTx];
    signal input balance1[nTx];
    signal input ay1[nTx];
    signal input ethAddr1[nTx];
    signal input siblings1[nTx][nLevels+1];
    // Required for inserts and deletes
    signal input isOld0_1[nTx];
    signal input oldKey1[nTx];
    signal input oldValue1[nTx];

    // State 2
    signal input tokenID2[nTx];
    signal input nonce2[nTx];
    signal input sign2[nTx];
    signal input balance2[nTx];
    signal input ay2[nTx];
    signal input ethAddr2[nTx];
    signal input siblings2[nTx][nLevels+1];
    signal input newExit[nTx];
    // Required for inserts and deletes
    signal input isOld0_2[nTx];
    signal input oldKey2[nTx];
    signal input oldValue2[nTx];

    // fee tx
    // State fees
    signal input tokenID3[maxFeeTx];
    signal input nonce3[maxFeeTx];
    signal input sign3[maxFeeTx];
    signal input balance3[maxFeeTx];
    signal input ay3[maxFeeTx];
    signal input ethAddr3[maxFeeTx];
    signal input siblings3[maxFeeTx][nLevels+1];

    var i;
    var j;

    component decodeTx[nTx];
    component rollupTx[nTx];
    component feeTx[maxFeeTx];

    // decode tx data
    ////////
    for (i = 0; i < nTx; i++) {
        decodeTx[i] = DecodeTx(nLevels);

        if (i == 0) {
            decodeTx[i].previousOnChain <== 1;
            decodeTx[i].inIdx <== oldLastIdx;
        } else {
            decodeTx[i].previousOnChain <== imOnChain[i-1];
            decodeTx[i].inIdx <== imOutIdx[i-1];
        }
        decodeTx[i].txCompressedData <== txCompressedData[i];
        decodeTx[i].toEthAddr <== toEthAddr[i];
        decodeTx[i].toBjjAy <== toBjjAy[i];
        decodeTx[i].rqTxCompressedDataV2 <== rqTxCompressedDataV2[i];
        decodeTx[i].rqToEthAddr <== rqToEthAddr[i];
        decodeTx[i].rqToBjjAy <== rqToBjjAy[i];

        decodeTx[i].fromEthAddr <== fromEthAddr[i];
        decodeTx[i].loadAmountF <== loadAmountF[i];
        for (j = 0; j < 256; j++){
            decodeTx[i].fromBjjCompressed[j] <== fromBjjCompressed[i][j];
        }

        decodeTx[i].globalChainID <== globalChainID;
        decodeTx[i].onChain <== onChain[i];
        decodeTx[i].newAccount <== newAccount[i];
        decodeTx[i].auxFromIdx <== auxFromIdx[i];
    }

    // Check txCompressedDataV2
    for (i = 0; i < nTx; i++) {
        decodeTx[i].txCompressedDataV2 === txCompressedDataV2[i];
    }

    // Check decode-tx intermediary signals
    for (i = 0; i < nTx - 1; i++) {
        decodeTx[i].onChain === imOnChain[i];
        decodeTx[i].outIdx === imOutIdx[i];
    }

    // rollup tx
    ////////
    for (i = 0; i < nTx; i++) {
        rollupTx[i] = RollupTx(nLevels, maxFeeTx);

        // accumulate fees
        for (j = 0; j < maxFeeTx; j++) {
            rollupTx[i].feePlanTokens[j] <== feePlanTokens[j];
        }
        if (i == 0) {
            for (j = 0; j < maxFeeTx; j++){
                rollupTx[i].accFeeIn[j] <== 0;
            }
        } else {
            for (j = 0; j < maxFeeTx; j++){
                rollupTx[i].accFeeIn[j] <== imAccFeeOut[i-1][j];
            }
        }

        // future and past data
        for (j = 0; j < 3; j++) {
            if (i+j+1 < nTx) {
                rollupTx[i].futureTxCompressedDataV2[j] <== txCompressedDataV2[i+j+1];
                rollupTx[i].futureToEthAddr[j] <== toEthAddr[i+j+1];
                rollupTx[i].futureToBjjAy[j] <== toBjjAy[i+j+1];
            } else {
                rollupTx[i].futureTxCompressedDataV2[j] <== 0;
                rollupTx[i].futureToEthAddr[j] <== 0;
                rollupTx[i].futureToBjjAy[j] <== 0;
            }
        }

        for (j = 0; j < 4; j++) {
            if (i-j-1 >= 0) {
                rollupTx[i].pastTxCompressedDataV2[j] <== txCompressedDataV2[i-j-1];
                rollupTx[i].pastToEthAddr[j] <== toEthAddr[i-j-1];
                rollupTx[i].pastToBjjAy[j] <== toBjjAy[i-j-1];
            } else {
                rollupTx[i].pastTxCompressedDataV2[j] <== 0;
                rollupTx[i].pastToEthAddr[j] <== 0;
                rollupTx[i].pastToBjjAy[j] <== 0;
            }
        }

        rollupTx[i].fromIdx <== decodeTx[i].fromIdx;
        rollupTx[i].auxFromIdx <== auxFromIdx[i];

        rollupTx[i].toIdx <== decodeTx[i].toIdx;
        rollupTx[i].auxToIdx <== auxToIdx[i];
        rollupTx[i].toBjjAy <== toBjjAy[i];
        rollupTx[i].toBjjSign <== decodeTx[i].toBjjSign;
        rollupTx[i].toEthAddr <== toEthAddr[i];

        rollupTx[i].amount <== decodeTx[i].amount;
        rollupTx[i].tokenID <== decodeTx[i].tokenID;
        rollupTx[i].nonce <== decodeTx[i].nonce;
        rollupTx[i].userFee <== decodeTx[i].userFee;
        rollupTx[i].rqOffset <== rqOffset[i];
        rollupTx[i].onChain <== onChain[i];
        rollupTx[i].newAccount <== newAccount[i];

        rollupTx[i].rqTxCompressedDataV2 <== rqTxCompressedDataV2[i];
        rollupTx[i].rqToEthAddr <== rqToEthAddr[i];
        rollupTx[i].rqToBjjAy <== rqToBjjAy[i];

        rollupTx[i].sigL2Hash <== decodeTx[i].sigL2Hash;
        rollupTx[i].s <== s[i];
        rollupTx[i].r8x <== r8x[i];
        rollupTx[i].r8y <== r8y[i];

        rollupTx[i].fromEthAddr <== fromEthAddr[i];
        rollupTx[i].loadAmountF <== loadAmountF[i];
        for (j = 0; j < 256; j++){
            rollupTx[i].fromBjjCompressed[j] <== fromBjjCompressed[i][j];
        }

        // State 1
        rollupTx[i].tokenID1 <== tokenID1[i];
        rollupTx[i].nonce1 <== nonce1[i];
        rollupTx[i].sign1 <== sign1[i];
        rollupTx[i].balance1 <== balance1[i];
        rollupTx[i].ay1 <== ay1[i];
        rollupTx[i].ethAddr1 <== ethAddr1[i];
        for (j = 0; j < nLevels+1; j++) {
            rollupTx[i].siblings1[j] <== siblings1[i][j];
        }
        rollupTx[i].isOld0_1 <== isOld0_1[i];
        rollupTx[i].oldKey1 <== oldKey1[i];
        rollupTx[i].oldValue1 <== oldValue1[i];

        // State 2
        rollupTx[i].tokenID2 <== tokenID2[i];
        rollupTx[i].nonce2 <== nonce2[i];
        rollupTx[i].sign2 <== sign2[i];
        rollupTx[i].balance2 <== balance2[i];
        rollupTx[i].newExit <== newExit[i];
        rollupTx[i].ay2 <== ay2[i];
        rollupTx[i].ethAddr2 <== ethAddr2[i];
        for (j = 0; j < nLevels+1; j++) {
            rollupTx[i].siblings2[j] <== siblings2[i][j];
        }
        rollupTx[i].isOld0_2 <== isOld0_2[i];
        rollupTx[i].oldKey2 <== oldKey2[i];
        rollupTx[i].oldValue2 <== oldValue2[i];

        if (i == 0) {
            rollupTx[i].oldStateRoot <== oldStateRoot;
            rollupTx[i].oldExitRoot <== 0;
        } else {
            rollupTx[i].oldStateRoot <== imStateRoot[i-1];
            rollupTx[i].oldExitRoot <== imExitRoot[i-1];
        }
    }
    // check rollup transaction intermediary signals
    for (i = 0; i < nTx-1; i++) {
        rollupTx[i].newStateRoot  === imStateRoot[i];
        rollupTx[i].newExitRoot  === imExitRoot[i];
        for (j = 0; j < maxFeeTx; j++){
            rollupTx[i].accFeeOut[j]  === imAccFeeOut[i][j];
        }
    }

    // fee transactions
    //////
    for (i = 0; i < maxFeeTx; i++) {
        feeTx[i] = FeeTx(nLevels);

        if (i == 0){
            feeTx[i].oldStateRoot <== imInitStateRootFee;
        } else {
            feeTx[i].oldStateRoot <== imStateRootFee[i-1];
        }

        feeTx[i].feePlanToken <== feePlanTokens[i];
        feeTx[i].feeIdx <== feeIdxs[i];
        feeTx[i].accFee <== imFinalAccFee[i];

        // state vars
        feeTx[i].tokenID <== tokenID3[i];
        feeTx[i].nonce <== nonce3[i];
        feeTx[i].sign <== sign3[i];
        feeTx[i].balance <== balance3[i];
        feeTx[i].ay <== ay3[i];
        feeTx[i].ethAddr <== ethAddr3[i];

        for (j = 0; j < nLevels+1; j++) {
            feeTx[i].siblings[j] <== siblings3[i][j];
        }
    }
    // check fee transaction intermediary signals
    for (i = 0; i < maxFeeTx-1; i++) {
        feeTx[i].newStateRoot  === imStateRootFee[i];
    }

    // check initial fee state root / accumulate fees for fee tx
    rollupTx[nTx-1].newStateRoot === imInitStateRootFee;

    for (i = 0; i < maxFeeTx; i++){
        rollupTx[nTx-1].accFeeOut[i] === imFinalAccFee[i];
    }

    // hash inputs
    ////////
    component hasherInputs = HashInputs(nLevels, nTx, maxL1Tx, maxFeeTx);

    hasherInputs.oldLastIdx <== oldLastIdx;
    hasherInputs.newLastIdx <== decodeTx[nTx-1].outIdx;
    hasherInputs.oldStateRoot <== oldStateRoot;
    hasherInputs.newStateRoot <== feeTx[maxFeeTx-1].newStateRoot;
    hasherInputs.newExitRoot <== rollupTx[nTx-1].newExitRoot;

    var bitsSingleL1TxsData = (2*48 + 32 + 16 + 16 + 256 + 160);
    for (i = 0; i < maxL1Tx; i++){
        for (j = 0; j < bitsSingleL1TxsData; j++ ){
            hasherInputs.L1TxsData[i*bitsSingleL1TxsData + j] <== decodeTx[i].L1TxData[j];
        }
    }

    var bitsSingleL2TxsData = (2*nLevels + 16 + 8);
    for (i = 0; i < nTx; i++){
        for (j = 0; j < bitsSingleL2TxsData; j++ ){
            hasherInputs.L2TxsData[i*bitsSingleL2TxsData + j] <== decodeTx[i].L2TxData[j];
        }
    }

    for (i = 0; i < maxFeeTx; i++){
        hasherInputs.feeTxsData[i] <== feeIdxs[i];
    }

    hasherInputs.globalChainID <== globalChainID;

    // set output
    hashGlobalInputs <== hasherInputs.hashInputsOut;
}