#!/bin/bash

# this only prepares the net benchmarks (i.e. those with output signals)

declare -a arr=(
# "AliasCheck@aliascheck.circom"
"AND@gates.circom"
"BabyAdd@babyjub.circom"
# "BabyCheck@babyjub.circom"
"BabyDbl@babyjub.circom"
"BabyPbk@babyjub.circom"
"BinSub@binsub.circom"
"BinSum@binsum.circom"
"BitElementMulAny@escalarmulany.circom"
"Bits2Num_strict@bitify.circom"
"Bits2Num@bitify.circom"
"Bits2Point_Strict@pointbits.circom"
"CompConstant@compconstant.circom"
"Decoder@multiplexer.circom"
# "EdDSAMiMCSpongeVerifier@eddsamimcsponge.circom"
# "EdDSAMiMCVerifier@eddsamimc.circom"
# "EdDSAPoseidonVerifier@eddsaposeidon.circom"
# "EdDSAVerifier@eddsa.circom"
"Edwards2Montgomery@montgomery.circom"
"EscalarMulAny@escalarmulany.circom"
"EscalarProduct@multiplexer.circom"
# "ForceEqualIfEnabled@comparators.circom"
"GreaterEqThan@comparators.circom"
"GreaterThan@comparators.circom"
"IsEqual@comparators.circom"
"IsZero@comparators.circom"
"LessEqThan@comparators.circom"
"LessThan@comparators.circom"
"MiMC7@mimc.circom"
"MiMCFeistel@mimcsponge.circom"
"MiMCSponge@mimcsponge.circom"
"Montgomery2Edwards@montgomery.circom"
"MontgomeryAdd@montgomery.circom"
"MontgomeryDouble@montgomery.circom"
"MultiAND@gates.circom"
"MultiMiMC7@mimc.circom"
"MultiMux1@mux1.circom"
"MultiMux2@mux2.circom"
"MultiMux3@mux3.circom"
"MultiMux4@mux4.circom"
"Multiplexer@multiplexer.circom"
"Multiplexor2@escalarmulany.circom"
"Mux1@mux1.circom"
"Mux2@mux2.circom"
"Mux3@mux3.circom"
"Mux4@mux4.circom"
"NAND@gates.circom"
"NOR@gates.circom"
"NOT@gates.circom"
"Num2Bits_strict@bitify.circom"
"Num2Bits@bitify.circom"
"Num2BitsNeg@bitify.circom"
"OR@gates.circom"
"Pedersen@pedersen_old.circom"
"Pedersen@pedersen.circom"
"Point2Bits_Strict@pointbits.circom"
"Poseidon@poseidon.circom"
"Segment@pedersen.circom"
"SegmentMulAny@escalarmulany.circom"
"SegmentMulFix@escalarmulfix.circom"
"Sigma@poseidon.circom"
"Sign@sign.circom"
"Switcher@switcher.circom"
"Window4@pedersen.circom"
"WindowMulFix@escalarmulfix.circom"
"XOR@gates.circom"
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
	circom -o ./benchmarks/circomlib-cff5ab6/ ./benchmarks/circomlib-cff5ab6/${fn} --r1cs --sym --O0
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/circomlib/${fn} > ./benchmarks/circomlib/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib/${bn}.r1cs > ./benchmarks/circomlib/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done
