#!/usr/bin/env bash

# Script used for invoking Picus from Docker.
# Instructions: set the following environment variables before calling this
# script, then run this script with no arguments.

# example usage
#   CIRCOM_SRC_DIR=./tmp/circomlib-79d3034/ MAIN_FILES=test-mimcsponge.circom SOLVER=cvc5 VERSION=v2 CEXP=true CIRCOM_OUT_DIR=./tmp/circomlib-79d3034/ TIMEOUT=5000 ./resources/docker_entrypoint.sh

# The folder containing all source files, including libraries.
CIRCOM_SRC_DIR="${CIRCOM_SRC_DIR:-/src_files}"

# A colon-separated list of folders/files in CIRCOM_SRC_DIR that Picus should
# be run on.
MAIN_FILES="${MAIN_FILES:-${CIRCOM_SRC_DIR}}"

# The folder where the circom output and picus logs should be stored.
CIRCOM_OUT_DIR="${CIRCOM_OUT_DIR:-/artifact_dir}"

# The backend solver that picus should use.
SOLVER="${SOLVER:-z3}"

# The picus version to use.
VERSION="${VERSION:-v3}"

# The timeout argument in milliseconds.
#   - For v0 it's the timeout for the whole solving.
#   - For other versions it's the timeout for each solver query.
TIMEOUT="${TIMEOUT:-5000}"

# Whether or not to print out counter-example. This only applies to version "v2".
# If using other versions, CEXP will be forced to false.
CEXP=${CEXP:-false}
if [ "${VERSION}" != "v2" ]; then
    # forced to false
    CEXP=false
fi
# Reveal the corresponding argument
ARGCEXP=""
if [ "${CEXP}" = true ]; then
    ARGCEXP="--get-model"
fi

set -e

mkdir -p "$CIRCOM_OUT_DIR"

# Run circom compiler
echo "Running circom compiler..."
for main_loc in $(xargs -n1 -d: <<< "$MAIN_FILES"); do
    for f in $(find "$main_loc" -type f -name '*.circom'); do
        echo "Compile: $f"
        out_dir=$(dirname $(realpath --relative-to="$CIRCOM_SRC_DIR" "$f"))
        mkdir -p "${CIRCOM_OUT_DIR}"/"$out_dir"
        circom -o "${CIRCOM_OUT_DIR}"/"$out_dir" "$f" --r1cs --sym --O0 --json
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
    racket test-${VERSION}-uniqueness.rkt --r1cs "$f" --solver cvc5 --timeout ${TIMEOUT} --weak ${ARGCEXP} |& tee "$logfile"
    echo "Log saved to $logfile"
    echo "--------------------------------------------------------"
    echo
done
