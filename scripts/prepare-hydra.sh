#!/bin/bash

declare -a arr=(
"hydra-s1.circom"
)

# for fp in ./benchmarks/hydra-2010a65/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/hydra-2010a65/ ./benchmarks/hydra-2010a65/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/hydra-2010a65/ ./benchmarks/hydra-2010a65/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/hydra-2010a65/${fn} > ./benchmarks/hydra-2010a65/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/hydra-2010a65/${bn}.r1cs > ./benchmarks/hydra-2010a65/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done