#!/bin/bash

for fp in ./benchmarks/maci-9b1b1a6-fixed/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/maci-9b1b1a6-fixed/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/maci-9b1b1a6-fixed/ ./benchmarks/maci-9b1b1a6-fixed/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/maci-9b1b1a6-fixed/ ./benchmarks/maci-9b1b1a6-fixed/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/maci-9b1b1a6-fixed/${fn} > ./benchmarks/maci-9b1b1a6-fixed/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/maci-9b1b1a6-fixed/${bn}.r1cs > ./benchmarks/maci-9b1b1a6-fixed/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done