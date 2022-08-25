#!/bin/bash

for fp in ./benchmarks/iden3-core-56a08f9/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/iden3-core-56a08f9/ ./benchmarks/iden3-core-56a08f9/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/iden3-core-56a08f9/ ./benchmarks/iden3-core-56a08f9/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/iden3-core-56a08f9/${fn} > ./benchmarks/iden3-core-56a08f9/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/iden3-core-56a08f9/${bn}.r1cs > ./benchmarks/iden3-core-56a08f9/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done