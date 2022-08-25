#!/bin/bash

for fp in ./benchmarks/circomlib-matrix-d41bae3/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/circomlib-matrix-d41bae3/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/circomlib-matrix-d41bae3/ ./benchmarks/circomlib-matrix-d41bae3/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/circomlib-matrix-d41bae3/ ./benchmarks/circomlib-matrix-d41bae3/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/circomlib-matrix-d41bae3/${fn} > ./benchmarks/circomlib-matrix-d41bae3/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib-matrix-d41bae3/${bn}.r1cs > ./benchmarks/circomlib-matrix-d41bae3/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done