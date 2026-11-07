#!/usr/bin/env bash
# Solves each row of the table at the end of this script (an LLVM IR input, the
# problem, the Int reading or BV mode, the expected answer) with the direct
# LLVM frontend (-p llvmsafe/llvmterm, llvmsafebv/llvmtermbv) and the
# competition wrapper's MuVal configuration, and compares the answer with the
# expected one.  It asserts the verdict only: a timeout, a MAYBE or an error
# is a failure like a wrong answer, so the table holds only inputs answered
# within the budget.
#
#   script/llvmfront/check_verdicts.sh [PATTERN]
#
# PATTERN (an extended regular expression) keeps the rows whose input path
# matches it.  CoAR is the one script/llvmfront/dune.sh builds
# (_build_llvmfront/default/main.exe), run in the same development image
# (LLVMFRONT_IMAGE), two CPUs, 4 GB, 30 s per row.  Prints one line per row,
# then the count and DONE; exits 1 if a row's answer differs.
set -uo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
image=${LLVMFRONT_IMAGE:-coar-llvm-dev:20261022}
exe=_build_llvmfront/default/main.exe
pattern=${1:-.}
[ -x "$root/$exe" ] || { echo "error: $exe not built (script/llvmfront/dune.sh)" >&2; exit 2; }

# The table: the expected verdicts live here, as script/check_smoke.sh keeps its own.
table() {
  cat <<'TABLE'
# The direct translation's regression inputs (this script):
# INPUT PROBLEM READING EXPECTED, tab-separated.  INPUT is relative to the
# repository root; PROBLEM is safe (unreach-call) or term (termination);
# READING is math (the default), mod, unb, wrapu, wrapa, hoist, promote, scfg,
# licm or joins (the default reading with loop-invariant reads moved, loop
# cells held in registers, simplifycfg or licm run, or joins off cycles built
# in place; config/llvmfront/*.json), arb, modarb or wrapuarb (math, mod or
# wrapu with an overflowing signed operation yielding an arbitrary value), bv,
# bvwrapa or bvarb (BV mode with signed arithmetic wrapping, or with signed
# overflow yielding an arbitrary vector);
# EXPECTED is YES or NO.
# the new Ptr2Arr's calls: wrap marks, cuts, region arrays
test/llvmfront/inputs/wrap_const_true.ll	safe	mod	YES
test/llvmfront/inputs/wrap_nondet_true.ll	safe	mod	YES
test/llvmfront/inputs/wrap_nondet_true.ll	safe	math	YES
test/llvmfront/inputs/wrap_nondet_true.ll	safe	bv	YES
test/llvmfront/inputs/wrap_nondet_false.ll	safe	mod	NO
test/llvmfront/inputs/wrap_signed_true.ll	safe	mod	YES
test/llvmfront/inputs/cut_true.ll	safe	mod	YES
test/llvmfront/inputs/cut_false.ll	safe	mod	NO
test/llvmfront/inputs/cut_term_true.ll	term	mod	YES
test/llvmfront/inputs/region_arbitrary_false.ll	safe	mod	NO
test/llvmfront/inputs/fc_malloc_read_false.ll	safe	math	NO
test/llvmfront/inputs/fc_malloc_read_false.ll	safe	bv	NO
test/llvmfront/inputs/fc_uint_wrap_nondet_true.ll	safe	mod	YES
test/llvmfront/inputs/region_arbitrary_safe_false.ll	safe	math	NO
test/llvmfront/inputs/region_arbitrary_term_false.ll	term	math	NO
test/llvmfront/inputs/region_input_error_safe_true.ll	safe	math	YES
test/llvmfront/inputs/region_input_error_term_true.ll	term	math	YES
test/llvmfront/inputs/region_scalar_cell_safe_false.ll	safe	math	NO
test/llvmfront/inputs/region_static_after_safe_true.ll	safe	math	YES
# a return of a constant (tail-call check)
test/llvmfront/inputs/fc_ballrajamani_ret_const_safe_false.ll	safe	mod	NO
test/llvmfront/inputs/fc_ballrajamani_ret_const_safe_false.ll	safe	bv	NO
test/llvmfront/inputs/fc_ballrajamani_ret_const_term_true.ll	term	mod	YES
test/llvmfront/inputs/fc_ballrajamani_ret_const_lp64_term_true.ll	term	unb	YES
# the unbounded reading
test/llvmfront/inputs/fc_aprove_b14_unbounded_eq_term_true.ll	term	unb	YES
test/llvmfront/inputs/fc_aprove_b15_unbounded_eq_term_true.ll	term	unb	YES
test/llvmfront/inputs/unbounded_char_range_safe_true.ll	safe	unb	YES
test/llvmfront/inputs/unbounded_negmin_term_true.ll	term	unb	YES
test/llvmfront/inputs/unbounded_uint_max_safe_true.ll	safe	unb	YES
test/llvmfront/inputs/unbounded_NonTermination2_term_false.ll	term	unb	NO
test/llvmfront/inputs/unbounded_RecursiveMultiplication_term_true.ll	term	unb	YES
# an overflowing nsw result read across a call: the mathematical reading stops
# the execution (benchmarks/C/termination/simple/ compiled by clang 19)
test/llvmfront/inputs/unbounded_negmin_term_true.ll	term	math	YES
test/llvmfront/inputs/unbounded_RecursiveMultiplication_term_true.ll	term	math	YES
benchmarks/LLVM/simple/recursive_negation_at_int_min_true-termination.ll	term	math	YES
benchmarks/LLVM/simple/recursive_negation_at_int_min_true-termination.ll	term	unb	YES
benchmarks/LLVM/simple/recursive_negation_alternates_false-termination.ll	term	math	NO
benchmarks/LLVM/simple/recursive_negation_alternates_false-termination.ll	term	mod	NO
benchmarks/LLVM/simple/recursive_negation_wrapped_by_unsigned_false-termination.ll	term	mod	NO
test/llvmfront/inputs/int_bound_safe.ll	safe	unb	NO
test/llvmfront/inputs/int_bound_safe.ll	safe	math	YES
# the readings of signed overflow: undefined (the path stops), wrapping, and an
# arbitrary value of the type (each choice covered); the C872 input recurses
# forever when -INT_MIN may be INT_MIN again, so it is NO under both of the latter
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	math	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	arb	NO
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	wrapa	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	mod	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	modarb	NO
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	wrapu	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	wrapuarb	NO
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	bv	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	bvwrapa	YES
benchmarks/LLVM/simple/overflowed_sum_guards_loop_true-termination_false-termination-arbitrary.ll	term	bvarb	NO
benchmarks/LLVM/simple/rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.ll	term	math	YES
benchmarks/LLVM/simple/rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.ll	term	arb	NO
benchmarks/LLVM/simple/rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.ll	term	modarb	NO
benchmarks/LLVM/simple/rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.ll	term	bv	YES
benchmarks/LLVM/simple/rejected_left_shift_guards_loop_true-termination_false-termination-arbitrary.ll	term	bvarb	NO
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	math	YES
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	arb	NO
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	wrapa	YES
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	wrapuarb	NO
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	bv	YES
benchmarks/LLVM/simple/min_divided_by_minus_one_guards_loop_true-termination_false-termination-arbitrary.ll	term	bvarb	NO
benchmarks/LLVM/simple/recursive_negation_at_int_min_true-termination.ll	term	arb	NO
benchmarks/LLVM/simple/recursive_negation_at_int_min_true-termination.ll	term	bvwrapa	NO
# SV-COMP task functions and attributes
test/llvmfront/inputs/verifier_error_safe_false.ll	safe	math	NO
test/llvmfront/inputs/verifier_error_safe_true.ll	safe	math	YES
test/llvmfront/inputs/verifier_error_term_true.ll	term	math	YES
test/llvmfront/inputs/defined_assume_term_false.ll	term	math	NO
test/llvmfront/inputs/defined_assume_term_true.ll	term	math	YES
test/llvmfront/inputs/defined_nondet_string_term_true.ll	term	math	YES
test/llvmfront/inputs/defnondet_int_true.ll	safe	math	YES
test/llvmfront/inputs/pure_nondet_false.ll	safe	math	NO
test/llvmfront/inputs/noalias_scope_decl_false.ll	safe	math	NO
test/llvmfront/inputs/free_safe_true.ll	safe	math	YES
test/llvmfront/inputs/free_term_true.ll	term	math	YES
athena/llvm2lts/test/scope/leaf.ll	safe	math	NO
athena/llvm2lts/test/scope/voidmain.ll	safe	math	NO
athena/llvm2lts/test/scope/defnondet.ll	term	math	YES
athena/llvm2lts/test/scope/defassume.ll	term	math	YES
# a _Bool parameter, which clang copies into its slot through a zext
test/llvmfront/inputs/bool_param_assert_safe_true.ll	safe	math	YES
test/llvmfront/inputs/bool_param_assert_safe_false.ll	safe	math	NO
# library models
athena/llvm2lts/test/scope/randtime.ll	safe	math	YES
athena/llvm2lts/test/scope/randtime.ll	safe	bv	YES
athena/llvm2lts/test/scope/socket.ll	safe	math	YES
athena/llvm2lts/test/scope/socket.ll	safe	bv	YES
athena/llvm2lts/test/scope/byteswap.ll	safe	math	YES
athena/llvm2lts/test/scope/byteswap.ll	safe	mod	YES
athena/llvm2lts/test/scope/byteswap.ll	safe	bv	YES
athena/llvm2lts/test/scope/imaxabs.ll	safe	bv	YES
athena/llvm2lts/test/scope/imaxabs.ll	safe	wrapu	YES
test/llvmfront/inputs/bswap_roundtrip_true.ll	safe	math	YES
test/llvmfront/inputs/bswap_roundtrip_true.ll	safe	bv	YES
test/llvmfront/inputs/bswap_fixpoint_false.ll	safe	math	NO
test/llvmfront/inputs/bswap_fixpoint_false.ll	safe	bv	NO
# bit intrinsics (BV) and bitwise operations with a constant (Int)
athena/llvm2lts/test/translate/bitops_true.ll	safe	bv	YES
athena/llvm2lts/test/translate/bitops64_true.ll	safe	bv	YES
athena/llvm2lts/test/translate/bitops_false.ll	safe	bv	NO
athena/llvm2lts/test/intmodes/bitconst_true.ll	safe	math	YES
athena/llvm2lts/test/intmodes/bitconst_true.ll	safe	mod	YES
athena/llvm2lts/test/intmodes/bitconst_true.ll	safe	wrapu	YES
athena/llvm2lts/test/intmodes/bitconst_false.ll	safe	math	NO
athena/llvm2lts/test/intmodes/bitconst_false.ll	safe	unb	NO
athena/llvm2lts/test/intmodes/bitconst_false.ll	safe	wrapa	NO
test/llvmfront/inputs/bitc_sign_true.ll	safe	math	YES
test/llvmfront/inputs/bitc_sign_true.ll	safe	mod	YES
test/llvmfront/inputs/bitc_sign_true.ll	safe	unb	YES
# the wrapping readings
athena/llvm2lts/test/intmodes/array_range_true.ll	safe	wrapu	YES
athena/llvm2lts/test/intmodes/array_range_true.ll	safe	wrapa	YES
athena/llvm2lts/test/intmodes/conversion_true.ll	safe	wrapu	YES
athena/llvm2lts/test/intmodes/overflow_builtin_true.ll	safe	wrapa	YES
athena/llvm2lts/test/intmodes/signed_overflow_true.ll	safe	wrapu	YES
athena/llvm2lts/test/intmodes/signed_overflow_true.ll	safe	wrapa	NO
athena/llvm2lts/test/translate/nsw_true.ll	safe	wrapu	YES
athena/llvm2lts/test/translate/nsw_true.ll	safe	wrapa	NO
athena/llvm2lts/test/translate/unsigned_wrap_true.ll	safe	wrapu	YES
athena/llvm2lts/test/translate/unsigned_wrap_true.ll	safe	wrapa	YES
# the old Ptr2Arr with SemanticAugmentor (C_Mod)
test/llvmfront/inputs/semaug_HeizmannHoenickeLeikePodelski-ATVA2013-Fig6_term_true.ll	term	mod	YES
test/llvmfront/inputs/semaug_Bangalore-2_term_true.ll	term	mod	YES
test/llvmfront/inputs/semaug_Bangalore_v4_term_true.ll	term	mod	YES
test/llvmfront/inputs/hoist_ptrbound_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_condbound_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_condread_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_nested_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_otherregion_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_globalbound_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_storedec_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_calldec_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_aliasdec_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_memsetloop_term.ll	term	hoist	YES
test/llvmfront/inputs/hoist_nonterm_term.ll	term	hoist	NO
test/llvmfront/inputs/hoist_exituse_true.ll	safe	hoist	YES
test/llvmfront/inputs/hoist_zerotrip_true.ll	safe	hoist	YES
test/llvmfront/inputs/hoist_unreachfn_term.ll	term	hoist	YES
test/llvmfront/inputs/scfg_divreach_true.ll	safe	scfg	YES
test/llvmfront/inputs/scfg_divreach_false.ll	safe	scfg	NO
test/llvmfront/inputs/scfg_divloop_term.ll	term	scfg	YES
test/llvmfront/inputs/joins_join_term.ll	term	joins	YES
test/llvmfront/inputs/joins_phi_true.ll	safe	joins	YES
test/llvmfront/inputs/joins_phi2_false.ll	safe	joins	NO
test/llvmfront/inputs/licm_sink2_true.ll	safe	licm	YES
test/llvmfront/inputs/licm_dead_true.ll	safe	licm	YES
test/llvmfront/inputs/licm_deadcmp_term.ll	term	licm	YES
test/llvmfront/inputs/licm_r1a_term.ll	term	licm	YES
test/llvmfront/inputs/licm_r19_term.ll	term	licm	YES
test/llvmfront/inputs/licm_r19g_term.ll	term	licm	YES
test/llvmfront/inputs/licm_r22_term.ll	term	licm	YES
test/llvmfront/inputs/licm_r6b_false.ll	safe	licm	NO
test/llvmfront/inputs/promote_dec_term.ll	term	promote	YES
test/llvmfront/inputs/promote_p1_term.ll	term	promote	NO
test/llvmfront/inputs/promote_p3_term.ll	term	promote	YES
test/llvmfront/inputs/promote_p4a_true.ll	safe	promote	YES
test/llvmfront/inputs/promote_p5_true.ll	safe	promote	YES
test/llvmfront/inputs/promote_p6_false.ll	safe	promote	NO
test/llvmfront/inputs/promote_p7_term.ll	term	promote	YES
test/llvmfront/inputs/promote_p13_true.ll	safe	promote	YES
# struct values indexed through an array, a nondet wider in the IR than its
# C type, a switch on an i1 (benchmarks/LLVM/simple/)
benchmarks/LLVM/simple/insertvalue_array_element_true.ll	safe	math	YES
benchmarks/LLVM/simple/insertvalue_array_element_true.ll	safe	bv	YES
benchmarks/LLVM/simple/extractvalue_array_of_structs_true.ll	safe	math	YES
benchmarks/LLVM/simple/extractvalue_array_of_structs_true.ll	safe	bv	YES
benchmarks/LLVM/simple/nondet_char_declared_int_true.ll	safe	math	YES
benchmarks/LLVM/simple/nondet_char_declared_int_true.ll	safe	bv	YES
benchmarks/LLVM/simple/switch_on_bool_true.ll	safe	math	YES
benchmarks/LLVM/simple/switch_on_bool_true.ll	safe	bv	YES
TABLE
}

rows=$(table | grep -v '^#' | awk -F'\t' -v p="$pattern" 'NF == 4 && $1 ~ p')

docker run -i --rm --cpus=2 --memory=4g --user "$(id -u):$(id -g)" -e HOME=/tmp \
  -v "$root":/w -w /w "$image" bash -c '
exe=$1
config=./config/solver/muval_yesno.json
total=0 bad=0
while IFS=$(printf "\t") read -r input problem reading expected; do
  case $problem in safe) p=llvmsafe ;; term) p=llvmterm ;; *) echo "bad problem: $problem"; exit 2 ;; esac
  extra=()
  case $reading in
    math) ;;
    mod) extra=(--llvm-config config/llvmfront/modulo.json) ;;
    unb) extra=(--llvm-config config/llvmfront/unbounded.json) ;;
    wrapu) extra=(--llvm-config config/llvmfront/wrap_unsigned.json) ;;
    wrapa) extra=(--llvm-config config/llvmfront/wrap_all.json) ;;
    arb) extra=(--llvm-config config/llvmfront/arbitrary_value.json) ;;
    modarb) extra=(--llvm-config config/llvmfront/modulo_arbitrary_value.json) ;;
    wrapuarb) extra=(--llvm-config config/llvmfront/wrap_unsigned_arbitrary_value.json) ;;
    hoist) extra=(--llvm-config config/llvmfront/hoist.json) ;;
    promote) extra=(--llvm-config config/llvmfront/promote.json) ;;
    scfg) extra=(--llvm-config config/llvmfront/simplifycfg.json) ;;
    joins) extra=(--llvm-config config/llvmfront/inline_joins.json) ;;
    licm) extra=(--llvm-config config/llvmfront/licm.json) ;;
    bv) p=${p}bv ;;
    bvwrapa) p=${p}bv; extra=(--llvm-config config/llvmfront/wrap_all.json) ;;
    bvarb) p=${p}bv; extra=(--llvm-config config/llvmfront/arbitrary_value.json) ;;
    *) echo "bad reading: $reading"; exit 2 ;;
  esac
  out=$(timeout 30 "$exe" -c "$config" -p "$p" "${extra[@]}" "$input" 2>/tmp/err); rc=$?
  answer=$(printf "%s\n" "$out" | tail -1)
  [ $rc -eq 124 ] && answer=timeout
  [ -z "$answer" ] && answer="rc=$rc"
  total=$((total + 1))
  if [ "$answer" = "$expected" ]; then mark=ok; else mark=WRONG; bad=$((bad + 1)); fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$mark" "$input" "$problem" "$reading" "$expected" "$answer"
done
echo "$total rows, $bad not as expected"
[ $bad -eq 0 ]
' check "$exe" <<< "$rows"
status=$?
echo DONE
exit $status
