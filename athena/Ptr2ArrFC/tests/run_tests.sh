#!/bin/bash
# Acceptance run of the transformation on every test input.
#
# usage: tests/run_tests.sh [--identity]
#                           [--memory-safety|--memory-cleanup|--assume-safety]
#                           [--violation-markers=split|reach-error]
#                           [--memtrack-check=guess|fixpoint] [--memtrack-nonterminating]
#                           [--data-model=LP64|ILP32]
#                           [--wrap-integers[=unsigned|all]] [--check-overflow]
#                           [--integers=auto [--integers-eva=on|off]]
#                           OUTDIR [input.c ...]
#   (default inputs: tests/cases/*.c and the files named in tests/bench.list,
#    which are paths relative to the repository root)
#   --identity  run the identity transformation (stage M0: tests the tools)
#   --memory-safety, --memory-cleanup, --assume-safety
#               transform in that mode, and compare against the sanitizers'
#               verdict on the input (see tools/p2a_diff.py)
#   --violation-markers=reach-error
#               with --memory-safety or --memory-cleanup: every violation
#               calls reach_error() instead of the marker of its property
#   --memtrack-nonterminating
#               also check valid-memtrack where an execution that does not
#               halt passes (the probes never fire in the differential run)
#   --memtrack-check=fixpoint
#               with --memory-safety: the deterministic form of the
#               valid-memtrack check, which the differential run can report
#               (the guess form, the default, is run with the empty guess)
#   --data-model=ILP32
#               read every input as ILP32 (each ptr2arr run gets the option)
#               and compile every program with -m32
#   --wrap-integers
#               transform with explicit integer reductions: compared in the C
#               reading (the reductions are the identity), and in the
#               mathematical reading (column zreading: ptr2arr --z-reading
#               widens the integers to 128 bits and computes the reductions)
#   --integers=auto
#               the reading chosen per input, and the reductions Eva shows
#               needless left out: compared as --wrap-integers is (an input
#               given the fixed-width reading has no reductions, and its
#               zreading column shows how the mathematical reading departs)
#   --wrap-integers=all
#               the same with signed wrap-around: the input is compiled with
#               gcc's -fwrapv in both comparisons (tools/p2a_diff.py --fwrapv)
#   --check-overflow
#               transform with the signed-overflow checks; a seed on which the
#               input overflows must reach reach_error there
#               (tools/p2a_diff.py --check-overflow)
#   --uninit=nondet
#               transform with nondeterministic starting values of the
#               uninitialised local variables; the output is run with
#               generators that return zero (tools/p2a_diff.py --uninit
#               nondet), so it must match the input run with zeroed memory
#   --uninit=check
#               transform with the checks of uninitialised reads; a seed on
#               which the input reads a checked variable uninitialised (the
#               E-ACSL build of the input says where) must reach the marker
#               there (tools/p2a_diff.py --uninit check)
#
# For each input, in OUTDIR/<name>/:
#   transform  ptr2arr (--identity); its exit status (2 = refused as
#              unsupported, 1 = unreadable input or not implemented yet; the
#              reason is the last line of transform.log)
#   check      ptr2arr --check on the output (--allow-pointers with
#              --identity): the output is readable by the same front end,
#              holds no internal name and, unless allowed, no pointer
#   diff       tools/p2a_diff.py on the input and the output (RESULT line)
#   monitor    the input instrumented by ptr2arr --monitor, run on the same
#              seeds: ok, VIOLATION (the region partition is unsound for an
#              execution) or compile-fail
#   fixpoint   the output transformed again equals the output: same; or the
#              second and third transformations agree (stabilizes: the
#              printer's layout changes once, e.g. a labelled return split in
#              two); or differs
#   expect     the output's exit status on seed 1 (the program the
#              differential run compiled) against the one the input states
#              for this run in a comment among its first ten lines,
#              "p2a-expect: KEY=STATUS ...": KEY is the mode (normal,
#              memory-safety, memory-cleanup, assume-safety), followed by
#              "+nonterminating" for --memtrack-nonterminating, "+check-overflow"
#              for --check-overflow, "+wrap-all" for --wrap-integers=all,
#              "+uninit-nondet" for --uninit=nondet (read without it when
#              the input does not state it), "+uninit-check" for
#              --uninit=check, "+fixpoint"
#              for --memtrack-check=fixpoint and "+reach-error"
#              for --violation-markers=reach-error; a key with "+fixpoint"
#              that the input does not state is read without it (both forms
#              of the check must agree), and then without "+nonterminating"
#              (an execution that halts ends with the same status). STATUS
#              is an exit status, abort
#              (134) or timeout (124, the run is stopped after 2 seconds).
#              An output with choices (the guess form, the probes of
#              --memtrack-nonterminating) is run with every choice
#              (tools/p2a_memtrack_eq.py --guess-status), as a verifier
#              explores them. ok, FAIL:<status>, or - when the input states
#              none
# One line per input goes to OUTDIR/summary.tsv; the script ends with the
# counts of each column and the line DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/../.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
transform_args=(); check_args=(); mode=normal; zreading=; markers=split
model=LP64; dm_args=(); form=guess; nonterm=; int_suffix=; diff_int=()
uninit_suffix=; diff_uninit=()
while :; do
  case "${1:-}" in
    --identity) transform_args+=(--identity); check_args=(--allow-pointers); shift ;;
    --memory-safety|--memory-cleanup|--assume-safety) transform_args+=("$1"); mode=${1#--}; shift ;;
    --violation-markers=*) transform_args+=("$1"); markers=${1#*=}; shift ;;
    --memtrack-check=*) transform_args+=("$1"); form=${1#*=}; shift ;;
    --memtrack-nonterminating) transform_args+=("$1"); nonterm=+nonterminating; shift ;;
    --data-model=*) dm_args=("$1"); model=${1#*=}; shift ;;
    --wrap-integers|--wrap-integers=unsigned) transform_args+=("$1"); zreading=1; shift ;;
    --integers=auto|--integers-eva=on|--integers-eva=off) transform_args+=("$1"); zreading=1; shift ;;
    --wrap-integers=all)
      transform_args+=("$1"); zreading=1; int_suffix=+wrap-all; diff_int=(--fwrapv); shift ;;
    --check-overflow)
      transform_args+=("$1"); int_suffix=+check-overflow; diff_int=(--check-overflow); shift ;;
    --uninit=nondet)
      transform_args+=("$1"); uninit_suffix=+uninit-nondet; diff_uninit=(--uninit nondet); shift ;;
    --uninit=check)
      transform_args+=("$1"); uninit_suffix=+uninit-check; diff_uninit=(--uninit check); shift ;;
    *) break ;;
  esac
done
suffix=$int_suffix$uninit_suffix
[ "$markers" = reach-error ] && suffix="$suffix+reach-error"
# the key, then the key without +fixpoint (both forms must agree), then
# without +nonterminating (a halting execution gives the same status)
keys=("$mode$nonterm$suffix" "$mode$suffix")
[ "$form" = fixpoint ] && keys=("$mode$nonterm+fixpoint$suffix" "${keys[@]}")
# with --uninit=nondet the output runs with zero starting values, as the
# input does, so a key the input does not state for it is read without it
if [ "$uninit_suffix" = +uninit-nondet ]; then
  for k in "${keys[@]}"; do keys+=("${k%"$uninit_suffix"}"); done
fi

# The exit status the input [$1] states for its output in this run, or nothing.
expected_status() {
  local v k
  for k in "${keys[@]}"; do
    v=$(head -10 "$1" | sed -n 's/.*p2a-expect:\([^*]*\).*/\1/p' | head -1 \
        | tr ' ' '\n' | sed -n "s/^$k=//p" | head -1)
    [ -n "$v" ] && break
  done
  case "$v" in abort) echo 134 ;; timeout) echo 124 ;; *) echo "$v" ;; esac
}
out=${1:?usage: run_tests.sh [--identity] OUTDIR [input.c ...]}
shift
mkdir -p "$out"
out=$(cd "$out" && pwd)
[ -x "$exe" ] || { echo "missing $exe; build with: dune build --root $here"; exit 1; }

inputs=("$@")
if [ ${#inputs[@]} -eq 0 ]; then
  inputs=("$here"/tests/cases/*.c)
  while read -r f; do inputs+=("$repo/$f"); done < "$here/tests/bench.list"
fi

summary="$out/summary.tsv"
printf 'name\ttransform\tcheck\tdiff\tmonitor\tfixpoint\tzreading\texpect\n' > "$summary"
declare -A seen
for src in "${inputs[@]}"; do
  name=$(basename "$src" .c)
  # inputs from different directories may share a name
  base=$name; k=1
  while [ -n "${seen[$name]:-}" ]; do k=$((k + 1)); name="${base}_$k"; done
  seen[$name]=1
  d="$out/$name"
  rm -rf "$d"; mkdir -p "$d"
  "$exe" "${transform_args[@]}" "${dm_args[@]}" -o "$d/out.c" "$src" > "$d/transform.log" 2>&1
  t=$?
  c=-; df=-; mon=-; fp=-; zr=-; ex=-
  if [ $t -eq 0 ]; then
    "$exe" --check "${check_args[@]}" "${dm_args[@]}" "$d/out.c" > "$d/check.log" 2>&1
    c=$?
    mon_args=()
    if "$exe" --monitor "${dm_args[@]}" -o "$d/monitor.c" "$src" > "$d/monitor.log" 2>&1; then
      mon_args=(--monitor "$d/monitor.c")
    else
      mon=instrument-fail
    fi
    # the overflow oracle runs on the normalised input, whose evaluation
    # order is the output's (see tools/p2a_diff.py --check-overflow)
    san_src=()
    if [ "$int_suffix" = +check-overflow ] \
       && "$exe" --identity "${dm_args[@]}" -o "$d/ident.c" "$src" > "$d/ident.log" 2>&1; then
      san_src=(--sanitize-source "$d/ident.c")
    fi
    python3 "$here/tools/p2a_diff.py" --workdir "$d/diff" --mode "$mode" "${san_src[@]}" \
      --violation-markers "$markers" --data-model "$model" "${diff_int[@]}" "${diff_uninit[@]}" \
      "${mon_args[@]}" "$src" "$d/out.c" > "$d/diff.log" 2>&1
    df=$(grep '^RESULT' "$d/diff.log" | awk '{print $2}')
    [ -n "$df" ] || df=error
    if [ ${#mon_args[@]} -gt 0 ]; then
      mon=$(grep '^MONITOR' "$d/diff.log" | awk '{print $2}')
      [ -n "$mon" ] || mon=not-run
    fi
    want=$(expected_status "$src")
    if [ -n "$want" ]; then
      if [ -x "$d/diff/out.exe" ]; then
        if [ -f "$d/diff/p2a_guess.o" ]; then
          got=$(cd "$d/diff" && python3 "$here/tools/p2a_memtrack_eq.py" \
                  --guess-status ./out.exe --seed 1 --workdir . | awk '{print $1}')
          [ "$got" = timeout ] && got=124
          case "$got" in -*) got=$((128 - got)) ;; esac
        else
          (cd "$d/diff" && P2A_SEED=1 timeout 2 ./out.exe > /dev/null 2>&1)
          got=$?
        fi
        if [ "$got" = "$want" ]; then ex=ok; else ex="FAIL:$got"; fi
      else
        ex=no-program
      fi
    fi
    "$exe" --identity "${dm_args[@]}" -o "$d/out2.c" "$d/out.c" > "$d/fixpoint.log" 2>&1
    if [ $? -ne 0 ]; then fp=error
    elif cmp -s "$d/out.c" "$d/out2.c"; then fp=same
    else
      "$exe" --identity "${dm_args[@]}" -o "$d/out3.c" "$d/out2.c" > "$d/fixpoint3.log" 2>&1
      if [ $? -eq 0 ] && cmp -s "$d/out2.c" "$d/out3.c"; then fp=stabilizes
      else fp=differs
      fi
    fi
  fi
  if [ $t -eq 0 ] && [ -n "$zreading" ]; then
    if "$exe" --z-reading "${dm_args[@]}" -o "$d/zreading.c" "$d/out.c" > "$d/zreading.log" 2>&1; then
      zd_int=(); [ "$int_suffix" = +wrap-all ] && zd_int=(--fwrapv)
      # the zero generators of --uninit=nondet, read from the output's record
      [ "$uninit_suffix" = +uninit-nondet ] \
        && zd_int+=(--uninit nondet --uninit-record "$d/out.p2a.json" --uninit-wide)
      [ "$uninit_suffix" = +uninit-check ] \
        && zd_int+=(--uninit check --uninit-record "$d/out.p2a.json")
      python3 "$here/tools/p2a_diff.py" --workdir "$d/zdiff" --data-model "$model" \
        "${zd_int[@]}" "$src" "$d/zreading.c" > "$d/zdiff.log" 2>&1
      zr=$(grep '^RESULT' "$d/zdiff.log" | awk '{print $2}')
      [ -n "$zr" ] || zr=error
    else
      zr=zreading-fail
    fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$t" "$c" "$df" "$mon" "$fp" "$zr" "$ex" >> "$summary"
done

for col in 2 3 4 5 6 7 8; do
  echo "== $(head -1 "$summary" | cut -f$col)"
  tail -n +2 "$summary" | cut -f$col | sort | uniq -c
done
echo "inputs: $(($(wc -l < "$summary") - 1))"
echo DONE
