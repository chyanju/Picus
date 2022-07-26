#!/bin/bash

for fp in ./benchmarks/circompairing/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/circompairing/ ./benchmarks/circompairing/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/circompairing/ ./benchmarks/circompairing/${fn} --r1cs --sym --O0
	# circom ./benchmarks/circompairing/${fn}
	echo "    parsing..."
	./circom-parser/target/debug/parser ./benchmarks/circompairing/${fn} > ./benchmarks/circompairing/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circompairing/${bn}.r1cs > ./benchmarks/circompairing/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done