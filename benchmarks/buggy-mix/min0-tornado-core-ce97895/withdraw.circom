include "./bitify.circom";
include "./pedersen.circom";
include "./merkleTree.circom";

// computes Pedersen(nullifier + secret)
template CommitmentHasher() {
    signal input nullifier;
    signal input secret;

    signal output commitment;
    signal output nullifierHash;

    component commitmentHasher = Pedersen(496);
    component nullifierHasher = Pedersen(248);
    component nullifierBits = Num2Bits(248);
    component secretBits = Num2Bits(248);
    nullifierBits.in <== nullifier;
    secretBits.in <== secret;
    for (var i = 0; i < 248; i++) {
        nullifierHasher.in[i] <== nullifierBits.out[i];
        commitmentHasher.in[i] <== nullifierBits.out[i];
        commitmentHasher.in[i + 248] <== secretBits.out[i];
    }

    commitment <== commitmentHasher.out[0];
    nullifierHash <== nullifierHasher.out[0];
}

// Verifies that commitment that corresponds to given secret and nullifier is included in the merkle tree of deposits
template Withdraw(levels, rounds) {
    signal input root;
    signal input nullifierHash;
    signal input receiver; // not taking part in any computations
    signal input fee; // not taking part in any computations
    signal input nullifier;
    signal input secret;
    signal input pathElements[levels];
    signal input pathIndex[levels];

    // simplified by Picus: we just provide the commitment directly
    signal input hasherCommitment;

    // Picus verification output
    signal output vOut;

    component tree = MerkleTree(levels, rounds);
    tree.leaf <== hasherCommitment;
    tree.root <== root;
    for (var i = 0; i < levels; i++) {
        tree.pathElements[i] <== pathElements[i];
        tree.pathIndex[i] <== pathIndex[i];
    }

    vOut <== tree.vOut;
}

component main = Withdraw(2, 2);