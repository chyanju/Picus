#!/bin/bash

declare -a arr=(
"buggy-mix/circom-ecdsa/test-bigmod22.circom"
)

for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	dn="$(dirname "${arr[@]}")"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	circom -o ./benchmarks/${dn}/ ./benchmarks/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/${fn} > ./benchmarks/${bn}.json

done