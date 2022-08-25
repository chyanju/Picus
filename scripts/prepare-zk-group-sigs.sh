#!/bin/bash

for fp in ./benchmarks/zk-group-sigs-1337689-fixed/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/zk-group-sigs-1337689-fixed/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/zk-group-sigs-1337689-fixed/ ./benchmarks/zk-group-sigs-1337689-fixed/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/zk-group-sigs-1337689-fixed/ ./benchmarks/zk-group-sigs-1337689-fixed/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/zk-group-sigs-1337689-fixed/${fn} > ./benchmarks/zk-group-sigs-1337689-fixed/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/zk-group-sigs-1337689-fixed/${bn}.r1cs > ./benchmarks/zk-group-sigs-1337689-fixed/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done