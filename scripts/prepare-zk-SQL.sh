#!/bin/bash

declare -a arr=(
"delete.circom"
"insert.circom"
"select.circom"
"update.circom"
)

# for fp in ./benchmarks/zk-SQL-4c3626d/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/zk-SQL-4c3626d/ ./benchmarks/zk-SQL-4c3626d/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	circom -o ./benchmarks/zk-SQL-4c3626d/ ./benchmarks/zk-SQL-4c3626d/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/zk-SQL-4c3626d/${fn} > ./benchmarks/zk-SQL-4c3626d/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/zk-SQL-4c3626d/${bn}.r1cs > ./benchmarks/zk-SQL-4c3626d/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done