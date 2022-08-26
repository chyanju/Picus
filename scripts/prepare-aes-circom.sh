#!/bin/bash

for fp in ./benchmarks/aes-circom-0784f74/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/aes-circom-0784f74/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/aes-circom-0784f74/ ./benchmarks/aes-circom-0784f74/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/aes-circom-0784f74/ ./benchmarks/aes-circom-0784f74/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/aes-circom-0784f74/${fn} > ./benchmarks/aes-circom-0784f74/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/aes-circom-0784f74/${bn}.r1cs > ./benchmarks/aes-circom-0784f74/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done