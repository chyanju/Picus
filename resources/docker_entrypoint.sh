#!/usr/bin/env bash

# Script used for invoking Picus from Docker.
# Instructions: set the following environment variables before calling this
# script, then run this script with no arguments.

# The folder containing all source files, including libraries.
CIRCOM_SRC_DIR="${CIRCOM_SRC_DIR:-/src_files}"

# A colon-separated list of folders/files in CIRCOM_SRC_DIR that Picus should
# be run on.
MAIN_FILES="${MAIN_FILES:-${CIRCOM_SRC_DIR}}"

# The folder where the circom output and picus logs should be stored.
CIRCOM_OUT_DIR="${CIRCOM_OUT_DIR:-/artifact_dir}"

set -e

mkdir -p "$CIRCOM_OUT_DIR"

# Run circom compiler
echo "Running circom compiler..."
for main_loc in $(xargs -n1 -d: <<< "$MAIN_FILES"); do
    for f in $(find "$main_loc" -type f -name '*.circom'); do
        echo "Compile: $f"
        out_dir=$(dirname $(realpath --relative-to="$CIRCOM_SRC_DIR" "$f"))
        mkdir -p "${CIRCOM_OUT_DIR}"/"$out_dir"
        circom -o "${CIRCOM_OUT_DIR}"/"$out_dir" "$f" --r1cs --sym --O0
    done
done
echo "Done compiling."
echo

# Run uniqueness tests on r1cs files
echo "Running picus..."
for f in $(find "$CIRCOM_OUT_DIR" -type f -name '*.r1cs'); do
    echo "--------------------------------------------------------"
    echo "Running picus on: $f"
    fdir=$(dirname "$f")
    logfile="$fdir"/"$(basename "$f")".picus.log
    racket test-pp-uniqueness.rkt --r1cs "$f" --solver cvc5 --weak |& tee "$logfile"
    echo "Log saved to $logfile"
    echo "--------------------------------------------------------"
    echo
done
