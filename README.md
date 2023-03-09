# Picus

Picus is an implementation of the $\mathsf{QED}^2$ tool.

## Getting Started Guide

This section provides basic instructions on how to test out the tool for the kick-the-tires phase. We provide pre-built docker image, which is recommended.

### Building from Docker (Recommended)

```bash
docker build -t picus:v0 .
docker run -it --rm picus:v0 bash
```

### Building from Source

You can skip this section if you build the tool from Docker.

Building from source is not recommended if you just want to quickly run and check the results. Some dependencies require manual building and configuration, which is system specific. One only needs to make sure the following dependencies are satisfied before the tool / basic testing instructions can be executed.

#### Dependencies

- Racket (8.0+): https://racket-lang.org/
  - Rosette (4.0+): https://github.com/emina/rosette
    - `raco pkg install --auto rosette`
  - csv-reading: https://www.neilvandyke.org/racket/csv-reading/
    - `raco pkg install --auto csv-reading`
  - graph-lib: [https://pkgs.racket-lang.org/package/graph-lib](https://pkgs.racket-lang.org/package/graph-lib)
    - `raco pkg install --auto graph`
  - math-lib: [https://pkgs.racket-lang.org/package/math-lib](https://pkgs.racket-lang.org/package/math-lib)
    - `raco pkg install --auto math-lib`
- Rust: https://www.rust-lang.org/
  - for circom parser
- Node.js: https://nodejs.org/en/
  - for circom parser
- Circom (2.0.6 Required): https://docs.circom.io/
  - older version may touch buggy corner cases

- z3 solver (4.10.2+ Required): [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)
  - older version may touch buggy corner cases

- cvc5-ff: [https://github.com/alex-ozdemir/CVC4/tree/ff](https://github.com/alex-ozdemir/CVC4/tree/ff)
  - see installation instructions [here](./NOTES.md#installing-cvc5-ff)

### Basic Testing Instructions

First change the directory to the repo's root path:

```bash
cd Picus/
```

Then run the script to compile the basic benchmarks:

```bash
./scripts/prepare-circomlib.sh
```

This compiles all the "circomlib-utils" benchmarks, and won't throw any error if the environment is configured successfully.

Then test some benchmarks, e.g., the `Decoder` benchmark, run:

```bash
racket ./picus-dpvl-uniqueness.rkt --solver cvc5 --timeout 5000 --weak --r1cs ./benchmarks/circomlib-cff5ab6/Decoder@multiplexer.r1cs
```

A successful run will output logging info ***similar*** to the following (note that actual counter-example could be different due to potential stochastic search strategy in dependant libraries):

```
# r1cs file: ./benchmarks/circomlib-cff5ab6/Decoder@multiplexer.r1cs
# timeout: 5000
# solver: cvc5
# selector: counter
# precondition: ()
# propagation: #t
# smt: #f
# weak: #t
# map: #f
# number of wires: 5
# number of constraints: 4
# field size (how many bytes): 32
# inputs: (0 4).
# outputs: (1 2 3).
# targets: #<set: 1 2 3>.
# parsing original r1cs...
# xlist: (x0 x1 x2 x3 x4).
# alt-xlist (x0 y1 y2 y3 x4).
# parsing alternative r1cs...
# configuring precondition...
# unique: #<set:>.
# initial known-set #<set: 0 4>
# initial unknown-set #<set: 1 2 3>
# refined known-set: #<set: 0 4>
# refined unknown-set: #<set: 1 2 3>
  # propagation (linear lemma): none.
  # propagation (binary01 lemma): none.
  # propagation (basis2 lemma): none.
  # propagation (aboz lemma): none.
  # propagation (aboz lemma): none.
  # checking: (x1 y1), sat.
# final unknown set #<set: 1 2 3>.
# weak uniqueness: unsafe.
# counter-example:
  #hash((one . 1) (p . 0) (ps1 . 21888242871839275222246405745257275088548364400416034343698204186575808495616) (ps2 . 21888242871839275222246405745257275088548364400416034343698204186575808495615) (ps3 . 21888242871839275222246405745257275088548364400416034343698204186575808495614) (ps4 . 21888242871839275222246405745257275088548364400416034343698204186575808495613) (ps5 . 21888242871839275222246405745257275088548364400416034343698204186575808495612) (x0 . 0) (x1 . 1) (x2 . 0) (x3 . 1) (x4 . 0) (y1 . 0) (y2 . 0) (y3 . 0) (zero . 0)).
```

If you see this, it means the environment that you are operating on is configured successfully.

## Step-by-Step Instructions

This section will explain how to reproduce all experimental results that support the conclusions in the paper. Please make sure you first of all follow the "Getting Started Guide" and are able to produce all the desired results, before continuing to the rest of this section.

This section shows instructions to reproduce results in Table 1, Table 2 and Figure 11, which are the main results of the paper.

### Experiment Perparation

We first create a "log" folder to store all the results and outputs generated during the experiment:

```bash
cd Picus/
mkdir logs/
```

We need to first compile all benchmarks. There are two sets: "circomlib-utils" (corresponding to the "circomlib" folder) and "circomlib-core" (corresponding to the "circomlibex" folder). Simply run the following from the repo's root path:

```bash
./scripts/prepare-circomlib.sh > ./logs/compile-utils.log 2>&1
```

and

```bash
./scripts/prepare-circomlibex.sh > ./logs/compile-core.log 2>&1
```

No error will be given if the environment is configured successfully. The total compilation will take less than 5 mins.

Note: There's a rare chance that some benchmarks may end up with compilation errors. This is usually due to insufficient running memory on the host machine. Simply try to run the script again or increase the memory, until the error is gone.

### Running Experiments

We first run all the experiments before analyzing and collecting all the results. Note that experiment for each benchmark set could take ***up to 4~10 hours***, and "circom-core" benchmark set could take significantly longer time than "circom-utils".

#### Full-Fledged $\mathsf{QED}^2$ for Both Benchmark Sets

Run the tool on "circom-utils" benchmarks:

```bash
mkdir ./logs/full-utils/
./scripts/batch-run-picus.sh cvc5 600 ./logs/full-utils/ ./benchmarks/circomlib-cff5ab6/ > ./logs/full-utils.log 2>&1
```

Run the tool on "circom-core" benchmarks:

```bash
mkdir ./logs/full-core/
./scripts/batch-run-picus.sh cvc5 600 ./logs/full-core/ ./benchmarks/circomlibex-cff5ab6/ > ./logs/full-core.log 2>&1
```

#### $\mathsf{QED^2}\mathsf{-UCP}$ for Both Benchmark Sets

Run the tool on "circom-utils" benchmarks:

```bash
mkdir ./logs/ucp-utils/
./scripts/batch-run-picus-nosolve.sh cvc5 600 ./logs/ucp-utils/ ./benchmarks/circomlib-cff5ab6/ > ./logs/ucp-utils.log 2>&1
```

Run the tool on "circom-core" benchmarks:

```bash
mkdir ./logs/ucp-core/
./scripts/batch-run-picus-nosolve.sh cvc5 600 ./logs/ucp-core/ ./benchmarks/circomlibex-cff5ab6/ > ./logs/ucp-core.log 2>&1
```

#### $\mathsf{QED^2}\mathsf{-SMT}$ for Both Benchmark Sets

Run the tool on "circom-utils" benchmarks:

```bash
mkdir ./logs/smt-utils/
./scripts/batch-run-picus-noprop.sh cvc5 600 ./logs/smt-utils/ ./benchmarks/circomlib-cff5ab6/ > ./logs/smt-utils.log 2>&1
```

Run the tool on "circom-core" benchmarks:

```bash
mkdir ./logs/smt-core/
./scripts/batch-run-picus-noprop.sh cvc5 600 ./logs/smt-core/ ./benchmarks/circomlibex-cff5ab6/ > ./logs/smt-core.log 2>&1
```

#### Extra Counter-Example Generation Procedure

One benchmark needs the extra counter-example generation procedure to find the bigger counter-example. Simply run the following command to check it out:

```bash
racket ./picus-cex-uniqueness.rkt --solver cvc5 --weak --r1cs ./benchmarks/circomlib-cff5ab6/BitElementMulAny\@escalarmulany.r1cs
```

It will output `unsafe` with a concrete `counter-example`.

### Parsing Results

After all the experiments are done, open `scripts/parse-results.ipynb` in a Jupyter Notebook/Lab (or use `scripts/parse-results.py` instead in terminal: `cd scripts/ && python ./parse-results.py`), and run the cells according to the notebook instructions to parse and print all the results claimed in the paper. You'll need to manually modify the `SERIES` variable in the script to switch results between "utils" and "core" benchmark set. See comments in the script for more details

> Note: If you are reproducing the results in Docker, you may experience (significant) performance drop of the results due to Docker's virtualization mechanism. This would affect the averaged time reported in Table 2, and potentially the total number of solved benchmarks.

> Note: The circuit statistics of Table 2 presented is different from the results parsed in this artifact due to rounding errors and change of APIs. We are fixing that in the camera-ready version while this wouldn't affect the artifact's performance nor the conclusions since they are stats of the benchmarks themselves. In particular, the following cell values need to be updated:
>
> circomlib-utils, small, linear: 8 -> 7
>
> circomlib-utils, small, non-linear: 8 -> 7
>
> circomlib-utils, medium, linear: 171 -> 170
>
> circomlib-utils, large, witness: 3466 -> 3465
>
> circomlib-utils, large, total: 3572 -> 3571
>
> circomlib-core, small, in: 28 -> 27
>
> circomlib-core, small, witness: 12 -> 11
>
> circomlib-core, small, total: 25 -> 49
>
> circomlib-core, medium, out: 28 -> 81
>
> circomlib-core, medium, witness: 392 -> 391
>
> circomlib-core, medium, non-linear: 275 -> 274
>
> circomlib-core, medium, total: 499 -> 472
>
> circomlib-core, large, out: 42 -> 41
>
> circomlib-core, large, witness: 34103 -> 34102
>
> circomlib-core, large, total: 34311 -> 34310
>
> circomlib-core, large, total: 34191 -> 34190

## Reusability Instructions

### Quick Problem Solving for New Circuits/Benchmarks

We also provide easy API to compile and solve for any new benchmarks created. First you can use the following script to compile arbitrary benchmark:

```bash
./picus-compile.sh <path-to-your-circom-file>
```

This will generate a `*.r1cs` file in the same path as your provided `*.circom` file. Then, use the following script to solve for the benchmark:

```bash
./picus-solve.sh <path-to-your-r1cs-file>
```

This will automatically invoke the tool and output the result.

### More Options and APIs of the Tool

The following lists out all available options for running the tool.

```bash
usage: picus-dpvl-uniqueness.rkt [ <option> ... ]

<option> is one of

  --r1cs <p-r1cs>
     path to target r1cs
  --timeout <p-timeout>
     timeout for every small query (default: 5000ms)
  --solver <p-solver>
     solver to use: z3 | cvc4 | cvc5 (default: z3)
  --selector <p-selector>
     selector to use: first | counter (default: counter)
  --precondition <p-precondition>
     path to precondition json (default: null)
  --noprop
     disable propagation (default: false / propagation on)
  --smt
     show path to generated smt files (default: false)
  --weak
     only check weak safety, not strong safety  (default: false)
  --map
     map the r1cs signals of model to its circom variable (default: true)
  --help, -h
     Show this help
  --
     Do not treat any remaining argument as a switch (at this level)

 Multiple single-letter switches can be combined after
 one `-`. For example, `-h-` is the same as `-h --`.
```
