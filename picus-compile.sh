#!/bin/bash
# usage:
#   picus-compile.sh <path-to-circom-file>

fp=$1
fd="$(dirname "${fp}")"
fn="$(basename "${fp}")"
bn="${fn%.*}"

# echo "# preparing: ${fp}"
circom -o ${fd} ${fp} --r1cs --sym --O0 > /dev/null 2>&1
