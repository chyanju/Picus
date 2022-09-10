#!/bin/bash
# usage: this.sh <timeout:seconds> <log_path> <target_folder>
# example: ./batch-run-picus.sh 600 ./logs/test/ ./benchmarks/circomlib-cff5ab6/

otime=$1
logpath=$2
targetfolder=$3

mkdir -p ${logpath}

for fp in ${targetfolder}/*.r1cs
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
    bp="${fp%.*}"
	echo "=================== checking: ${fn} ==================="
    timeout ${otime} racket ./test-v3-uniqueness.rkt --timeout 5000 --solver cvc5 --initlvl 0 --weak --r1cs ${fp} > ${logpath}/${bn}.log 2>&1
done