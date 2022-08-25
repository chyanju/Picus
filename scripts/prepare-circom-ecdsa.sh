#!/bin/bash

for fp in ./benchmarks/circom-ecdsa-d87eb70/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/circom-ecdsa-d87eb70/ ./benchmarks/circom-ecdsa-d87eb70/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/circom-ecdsa-d87eb70/ ./benchmarks/circom-ecdsa-d87eb70/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/circom-ecdsa-d87eb70/${fn} > ./benchmarks/circom-ecdsa-d87eb70/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circom-ecdsa-d87eb70/${bn}.r1cs > ./benchmarks/circom-ecdsa-d87eb70/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done