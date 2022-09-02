#!/bin/bash

otime=$1
targetfolder=$2


for fp in ${targetfolder}/*.r1cs
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== checking: ${fn} ==================="
    timeout ${otime} racket ./test-pp-uniqueness.rkt --timeout 5000 --solver cvc5 --initlvl 0 --weak --r1cs ${fp} > ./logs/${bn}.log 2>&1
done