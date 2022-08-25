#!/bin/bash

declare -a arr=(
"biomebase.circom"
"init.circom"
"move.circom"
"test_perlin.circom"
"test_range_proof.circom"
"reveal.circom"
"whitelist.circom"
)

# for fp in ./benchmarks/darkforest-eth-9033eaf-fixed/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/darkforest-eth-9033eaf-fixed/ ./benchmarks/darkforest-eth-9033eaf-fixed/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/darkforest-eth-9033eaf-fixed/ ./benchmarks/darkforest-eth-9033eaf-fixed/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/darkforest-eth-9033eaf-fixed/${fn} > ./benchmarks/darkforest-eth-9033eaf-fixed/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/darkforest-eth-9033eaf-fixed/${bn}.r1cs > ./benchmarks/darkforest-eth-9033eaf-fixed/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done