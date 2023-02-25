#!/bin/bash

for fp in ./benchmarks/circom-pairing-ext-743d761/*.circom
do
	fn=$(basename ${fp})
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	circom -o ./benchmarks/circom-pairing-ext-743d761/ ./benchmarks/circom-pairing-ext-743d761/${fn} --r1cs --sym --O0

done