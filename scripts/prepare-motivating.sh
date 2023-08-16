#!/bin/bash

declare -a arr=(
# "ValidateDecodingFixed.circom"
# "ValidateDecodingBuggy.circom"
"VDBuggy.circom"
"VDFixed.circom"
"adder.circom"
)

# for fp in ./benchmarks/circomlib/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/circomlib/ ./benchmarks/circomlib/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	#  /home/clara/circom/iden3_circom_now/target/release/circom -o ../benchmarks/circomlib-cff5ab6/ ../benchmarks/circomlib-cff5ab6/${fn} --r1cs --sym --O0 --json
	circom -o ./benchmarks/motivating/ ./benchmarks/motivating/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/circomlib/${fn} > ./benchmarks/circomlib/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib/${bn}.r1cs > ./benchmarks/circomlib/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done
