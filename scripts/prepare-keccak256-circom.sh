#!/bin/bash

for fp in ./benchmarks/keccak256-circom-af3e898/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/keccak256-circom-af3e898/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/keccak256-circom-af3e898/ ./benchmarks/keccak256-circom-af3e898/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/keccak256-circom-af3e898/ ./benchmarks/keccak256-circom-af3e898/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/keccak256-circom-af3e898/${fn} > ./benchmarks/keccak256-circom-af3e898/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/keccak256-circom-af3e898/${bn}.r1cs > ./benchmarks/keccak256-circom-af3e898/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done