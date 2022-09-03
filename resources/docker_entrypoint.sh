#!/usr/bin/env bash

set -e

CIRCOM_SRC_DIR=${CIRCOM_SRC_DIR:-/src_files}
CIRCOM_OUT_DIR=${CIRCOM_OUT_DIR:-/artifact_dir}

mkdir -p "$CIRCOM_OUT_DIR"

# Run circom compiler
echo "Running circom compiler..."
for f in "$CIRCOM_SRC_DIR"/*.circom; do
    echo "Compile: $f"
    circom -o "${CIRCOM_OUT_DIR}" "$f" --r1cs --sym --O0
done
echo "Done compiling."
echo

# Run uniqueness tests on r1cs files
echo "Running picus..."
for f in "$CIRCOM_OUT_DIR"/*.r1cs; do
    echo "--------------------------------------------------------"
    echo "Running picus on: $f"
    racket test-pp-uniqueness.rkt --r1cs "$f" --solver cvc5 --weak
    echo "--------------------------------------------------------"
    echo
done
