#!/bin/bash

declare -a arr=(
"semaphore.circom"
)

# for fp in ./benchmarks/semaphore-0f0fc95/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/semaphore-0f0fc95/ ./benchmarks/semaphore-0f0fc95/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/semaphore-0f0fc95/ ./benchmarks/semaphore-0f0fc95/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/semaphore-0f0fc95/${fn} > ./benchmarks/semaphore-0f0fc95/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/semaphore-0f0fc95/${bn}.r1cs > ./benchmarks/semaphore-0f0fc95/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done