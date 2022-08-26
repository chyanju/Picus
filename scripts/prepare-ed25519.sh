#!/bin/bash

for fp in ./benchmarks/ed25519-099d19c-fixed/*.circom
do
	fn=$(basename ${fp})
	echo "${fn}"
done

for fp in ./benchmarks/ed25519-099d19c-fixed/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/ed25519-099d19c-fixed/ ./benchmarks/ed25519-099d19c-fixed/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/ed25519-099d19c-fixed/ ./benchmarks/ed25519-099d19c-fixed/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/ed25519-099d19c-fixed/${fn} > ./benchmarks/ed25519-099d19c-fixed/${bn}.json

	# don't do this since the constraints are quite large
	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/ed25519-099d19c-fixed/${bn}.r1cs > ./benchmarks/ed25519-099d19c-fixed/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done