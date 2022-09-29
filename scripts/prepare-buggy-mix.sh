#!/bin/bash

declare -a arr=(
"buggy-mix/circom-ecdsa-436665b/test-bigmod22.circom"
# "buggy-mix/hermez-network-971c89f/test-rollup-main-L1.circom"
# "buggy-mix/iden3-core-3a3a300/credentialAtomicQuerySigTest.circom"
)

for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	dn="$(dirname "${fn}")"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	circom -o ./benchmarks/${dn}/ ./benchmarks/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/${fn} > ./benchmarks/${bn}.json

done