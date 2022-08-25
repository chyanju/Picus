#!/bin/bash

declare -a arr=(
"AliasCheck@aliascheck.circom"
"BabyDbl@babyjub.circom"
"BabyAdd@babyjub.circom"
"BabyCheck@babyjub.circom"
"BabyPbk@babyjub.circom"
"BinSub@binsub.circom"
"BinSum@binsum.circom"
"Num2BitsNeg@bitify.circom"
"Num2Bits_strict@bitify.circom"
"Bits2Num@bitify.circom"
"Bits2Num_strict@bitify.circom"
"Num2Bits@bitify.circom"
"IsZero@comparators.circom"
"LessEqThan@comparators.circom"
"LessThan@comparators.circom"
"GreaterThan@comparators.circom"
"ForceEqualIfEnabled@comparators.circom"
"IsEqual@comparators.circom"
"GreaterEqThan@comparators.circom"
"CompConstant@compconstant.circom"
"EdDSAVerifier@eddsa.circom"
"EdDSAMiMCVerifier@eddsamimc.circom"
"EdDSAMiMCSpongeVerifier@eddsamimcsponge.circom"
"EdDSAPoseidonVerifier@eddsaposeidon.circom"
"BitElementMulAny@escalarmulany.circom"
"Multiplexor2@escalarmulany.circom"
"EscalarMulAny@escalarmulany.circom"
"SegmentMulAny@escalarmulany.circom"
"SegmentMulFix@escalarmulfix.circom"
"WindowMulFix@escalarmulfix.circom"
"NOR@gates.circom"
"MultiAND@gates.circom"
"NOT@gates.circom"
"NAND@gates.circom"
"OR@gates.circom"
"XOR@gates.circom"
"AND@gates.circom"
# "IsZero@isZero.circom" # isZero.circom is not in latest circomlib
"MiMC7@mimc.circom"
"MultiMiMC7@mimc.circom"
"MIMCFeistel@mimcsponge.circom"
"MiMCSponge@mimcsponge.circom"
"Edwards2Montgomery@montgomery.circom"
"Montgomery2Edwards@montgomery.circom"
"MontgomeryDouble@montgomery.circom"
"MontgomeryAdd@montgomery.circom"
"Multiplexer@multiplexer.circom"
"EscalarProduct@multiplexer.circom"
"Decoder@multiplexer.circom"
"Mux1@mux1.circom"
"MultiMux1@mux1.circom"
"MultiMux2@mux2.circom"
"Mux2@mux2.circom"
"MultiMux3@mux3.circom"
"Mux3@mux3.circom"
"MultiMux4@mux4.circom"
"Mux4@mux4.circom"
"Pedersen@pedersen_old.circom"
"Pedersen@pedersen.circom"
"Window4@pedersen.circom"
"Segment@pedersen.circom"
"Bits2Point_Strict@pointbits.circom"
"Point2Bits_Strict@pointbits.circom"
"Poseidon@poseidon.circom"
"Sigma@poseidon.circom"
"Sign@sign.circom"
"Switcher@switcher.circom"
)

# for fp in ./benchmarks/circomlib/*.circom
for fn in "${arr[@]}"
do
	bn="${fn%.*}"
	echo "=================== ${fn}: ${bn} ==================="
	echo "    compiling..."
	# circom -o ./benchmarks/circomlib/ ./benchmarks/circomlib/${fn} --r1cs --sym
	# to compare with Ecne, you need --O0 to disable optimization
	# /home/clara/circom/iden3_circom_now/target/release/circom -o ./benchmarks/circomlib/ ./benchmarks/circomlib/${fn} --r1cs --sym --O0 --json
	circom -o ./benchmarks/circomlib/ ./benchmarks/circomlib/${fn} --r1cs --sym --O0 --json
	# echo "    parsing..."
	# ./circom-parser/target/debug/parser ./benchmarks/circomlib/${fn} > ./benchmarks/circomlib/${bn}.json

	# echo "    reading..."
	# racket ./test-read-r1cs.rkt --r1cs ./benchmarks/circomlib/${bn}.r1cs > ./benchmarks/circomlib/${bn}.r1cs.log

	# echo "    testing..."
	# racket ./test-functionality.rkt --cname ${bn}
done
