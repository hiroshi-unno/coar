#!/bin/bash
# Generates simple/all_ops_unsat.btor2: a model with no state whose bad
# property says "some operator did not produce its expected value".  If `-p
# btor2` translates (and constant-folds) every operator faithfully, no bad
# state is reachable and the answer is `unsat` (the verdict in the file name is
# the Hardware Model Checking Competition's; see README.md).
# simple/all_ops_negative_sat.btor2 plants one wrong expectation, so that the
# check is shown to have teeth (expected `sat`).
#
# Expected values follow SMT-LIB FixedSizeBitVectors, which BTOR2 agrees with.
#
# Usage:
#   benchmarks/BTOR2/gen_ops.sh                    write the two models
#   benchmarks/BTOR2/gen_ops.sh --check [EXE] [CONFIG]
#                                                  write them, then run
#                                                  EXE -c CONFIG -p btor2 on each and compare the
#                                                  answer with the verdict in its name
#                                                  (defaults: ./_build/default/main.exe,
#                                                  ./config/solver/mucyc.json; run from the
#                                                  repository root)
set -eu
outdir=$(cd "$(dirname "$0")/simple" && pwd)

gen() {
  local plant_bug=$1
  N=0
  OUT=""
  CHECKS=()
  emit() {
    N=$((N + 1))
    OUT="$OUT$N $*
"
    R=$N
  }

  emit sort bitvec 8; S8=$R
  emit sort bitvec 1; S1=$R
  emit sort bitvec 4; S4=$R
  emit sort bitvec 16; S16=$R

  k() { emit constd "$1" "$2"; }

  # check that node $1 (of sort $2) equals the constant $3
  chk() {
    local node=$1 srt=$2 want=$3
    k "$srt" "$want"; local e=$R
    emit eq "$S1" "$node" "$e"
    CHECKS+=("$R")
  }

  # binary operator over sort $2 applied to constants $3 and $4, expecting $5
  b() {
    local op=$1 srt=$2 x=$3 y=$4 want=$5
    k "$srt" "$x"; local a=$R
    k "$srt" "$y"; local b=$R
    emit "$op" "$srt" "$a" "$b"; local r=$R
    chk "$r" "$srt" "$want"
  }

  # binary predicate (result of sort bitvec 1) over sort $2
  p() {
    local op=$1 srt=$2 x=$3 y=$4 want=$5
    k "$srt" "$x"; local a=$R
    k "$srt" "$y"; local b=$R
    emit "$op" "$S1" "$a" "$b"; local r=$R
    chk "$r" "$S1" "$want"
  }

  # unary operator over sort $2
  u() {
    local op=$1 srt=$2 x=$3 want=$4
    k "$srt" "$x"; local a=$R
    emit "$op" "$srt" "$a"; local r=$R
    chk "$r" "$srt" "$want"
  }

  # unary reduction to sort bitvec 1
  red() {
    local op=$1 x=$2 want=$3
    k "$S8" "$x"; local a=$R
    emit "$op" "$S1" "$a"; local r=$R
    chk "$r" "$S1" "$want"
  }

  # --- arithmetic, including wrap-around ---
  b add "$S8" 200 100 44
  b sub "$S8" 10 20 246
  b mul "$S8" 20 20 144
  u inc "$S8" 255 0
  u dec "$S8" 0 255
  u neg "$S8" 1 255
  u not "$S8" 0 255

  # --- division and remainder, including division by zero ---
  b udiv "$S8" 200 7 28
  b udiv "$S8" 5 0 255
  b urem "$S8" 200 7 4
  b urem "$S8" 5 0 5
  b sdiv "$S8" 249 2 253 # -7 / 2 = -3, truncating toward zero
  b sdiv "$S8" 7 0 255   # x / 0 = -1 for non-negative x
  b sdiv "$S8" 249 0 1   # -7 / 0 = 1
  b srem "$S8" 249 2 255 # -7 rem 2 = -1, sign of the dividend
  b smod "$S8" 249 2 1   # -7 mod 2 = 1, sign of the divisor

  # --- shifts, including a shift amount at or beyond the width ---
  b sll "$S8" 1 3 8
  b sll "$S8" 1 8 0
  b srl "$S8" 128 1 64
  b srl "$S8" 128 8 0
  b sra "$S8" 128 1 192
  b sra "$S8" 128 8 255
  b sra "$S8" 64 1 32

  # --- rotation by a variable amount ---
  b rol "$S8" 129 1 3
  b rol "$S8" 129 0 129
  b rol "$S8" 129 8 129
  b ror "$S8" 129 1 192
  b ror "$S8" 129 0 129

  # --- bitwise ---
  b and "$S8" 240 15 0
  b or "$S8" 240 15 255
  b xor "$S8" 255 15 240
  b nand "$S8" 255 255 0
  b nor "$S8" 0 0 255
  b xnor "$S8" 255 15 15

  # --- reductions ---
  red redand 255 1
  red redand 254 0
  red redor 0 0
  red redor 1 1
  red redxor 3 0
  red redxor 7 1
  red redxor 1 1

  # --- comparisons ---
  p ult "$S8" 1 2 1
  p ult "$S8" 2 1 0
  p ulte "$S8" 2 2 1
  p ugt "$S8" 2 1 1
  p ugte "$S8" 2 2 1
  p slt "$S8" 129 1 1 # -127 < 1
  p slte "$S8" 129 129 1
  p sgt "$S8" 1 129 1
  p sgte "$S8" 1 1 1
  p eq "$S8" 5 5 1
  p neq "$S8" 5 6 1

  # --- overflow predicates ---
  p uaddo "$S8" 200 100 1
  p uaddo "$S8" 100 100 0
  p saddo "$S8" 100 100 1
  p saddo "$S8" 1 1 0
  p usubo "$S8" 1 2 1
  p usubo "$S8" 2 1 0
  p ssubo "$S8" 128 1 1 # -128 - 1 underflows
  p ssubo "$S8" 1 1 0
  p umulo "$S8" 16 16 1
  p umulo "$S8" 15 15 0
  p smulo "$S8" 64 2 1
  p smulo "$S8" 10 10 0
  p sdivo "$S8" 128 255 1 # -128 / -1
  p sdivo "$S8" 1 255 0

  # --- width changing ---
  k "$S4" 10; A=$R
  k "$S4" 5; B=$R
  emit concat "$S8" "$A" "$B"; CC=$R
  chk "$CC" "$S8" 165
  emit slice "$S4" "$CC" 7 4; SL=$R
  chk "$SL" "$S4" 10
  k "$S4" 15; F=$R
  emit uext "$S8" "$F" 4; UE=$R
  chk "$UE" "$S8" 15
  k "$S4" 8; E=$R
  emit sext "$S8" "$E" 4; SE=$R
  chk "$SE" "$S8" 248 # -8 sign-extended
  emit uext "$S4" "$E" 0; U0=$R
  chk "$U0" "$S4" 8

  # --- ite, implies, iff on width 1 ---
  emit const "$S1" 1; ONE1=$R
  emit const "$S1" 0; ZERO1=$R
  k "$S8" 7; T7=$R
  k "$S8" 9; T9=$R
  emit ite "$S8" "$ONE1" "$T7" "$T9"; IT=$R
  chk "$IT" "$S8" 7
  emit ite "$S8" "$ZERO1" "$T7" "$T9"; IF=$R
  chk "$IF" "$S8" 9
  emit implies "$S1" "$ONE1" "$ZERO1"; IM=$R
  chk "$IM" "$S1" 0
  emit implies "$S1" "$ZERO1" "$ONE1"; IM2=$R
  chk "$IM2" "$S1" 1
  emit iff "$S1" "$ONE1" "$ONE1"; IFF=$R
  chk "$IFF" "$S1" 1
  emit iff "$S1" "$ONE1" "$ZERO1"; IFF2=$R
  chk "$IFF2" "$S1" 0

  # --- negated operand ids denote bitwise negation ---
  k "$S8" 15; NN=$R
  k "$S8" 0; Z0=$R
  emit add "$S8" "-$NN" "$Z0"; NEGREF=$R # (bvnot 15) + 0 = 240
  chk "$NEGREF" "$S8" 240

  # --- wider constants ---
  k "$S16" 65535; W=$R
  emit inc "$S16" "$W"; WI=$R
  chk "$WI" "$S16" 0

  if [ "$plant_bug" = yes ]; then
    # a deliberately wrong expectation, so the harness is known to detect one
    k "$S8" 1; X=$R
    k "$S8" 1; Y=$R
    emit add "$S8" "$X" "$Y"; W2=$R
    chk "$W2" "$S8" 3 # 1 + 1 is 2, not 3
  fi

  acc=${CHECKS[0]}
  for c in "${CHECKS[@]:1}"; do
    emit and "$S1" "$acc" "$c"
    acc=$R
  done
  emit not "$S1" "$acc"
  bad=$R
  emit bad "$bad"
  printf '%s' "$OUT"
}

{
  echo "; every operator applied to constants, compared with its expected value"
  echo "; generated by benchmarks/BTOR2/gen_ops.sh -- do not edit by hand"
  gen no
} >"$outdir/all_ops_unsat.btor2"

{
  echo "; same as all_ops_unsat but with one expectation deliberately wrong"
  echo "; generated by benchmarks/BTOR2/gen_ops.sh -- do not edit by hand"
  gen yes
} >"$outdir/all_ops_negative_sat.btor2"

echo "wrote all_ops_unsat.btor2 and all_ops_negative_sat.btor2"

[ "${1:-}" = --check ] || exit 0
exe=${2:-./_build/default/main.exe}
cfg=${3:-./config/solver/mucyc.json}
fail=0
for name in all_ops_unsat all_ops_negative_sat; do
  want=${name##*_}
  got=$("$exe" -c "$cfg" -p btor2 "$outdir/$name.btor2" | head -n 1)
  if [ "$got" = "$want" ]; then
    echo "ok   $name: $got"
  else
    echo "FAIL $name: expected $want, got $got"
    fail=1
  fi
done
exit $fail
