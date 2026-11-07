#!/bin/bash
# What --integers=auto decides on the inputs written to falsify it.
#
# usage: tests/integers_auto.sh [WORKDIR]
#
# Each case transforms one input of tests/cases with --integers=auto and
# checks the record's "integers" field (and, where the decision shows there,
# the output): a reduction that changes a value is kept, one the value
# analysis shows in range is left out, a recursive call graph turns the
# value analysis off, an & between two variables chooses the fixed-width
# reading, a shift count holding one value is replaced by it, a product that
# is non-negative but may leave the range gets the non-negative reduction,
# and a leaf at or above 2^(w-1) keeps its reduction. The exit status and the
# differential comparison are run_tests.sh's (--integers=auto); this script
# checks only the decisions. One line per case (ok or FAIL); the script ends
# with the counts and the line DONE, and exits 1 if a case failed.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe=${PTR2ARR_EXE:-"$here/_build/default/bin/ptr2arr.exe"}
[ -x "$exe" ] || { echo "missing $exe; build with: dune build --root $here"; exit 1; }
work=${1:-$(mktemp -d)}
mkdir -p "$work"
work=$(cd "$work" && pwd)

pass=0; fail=0
# check NAME PYTHON-CONDITION [GREP-OUT]: transform tests/cases/NAME.c; the
# condition reads the record's "integers" field as i; GREP-OUT, when given,
# is a pattern the output must contain ("!PATTERN": must not contain)
check() {
  local name=$1 cond=$2 pat=${3:-}
  local in="$here/tests/cases/$name.c" out="$work/$name.c" rec="$work/$name.json"
  local r=ok why=""
  if ! (cd "$work" && "$exe" --integers=auto -o "$out" --record="$rec" "$in") > "$work/$name.log" 2>&1; then
    r=FAIL; why="transform failed: $(tail -1 "$work/$name.log")"
  elif ! python3 -c "import json,sys; i=json.load(open(sys.argv[1]))['integers']; sys.exit(0 if ($cond) else 1)" "$rec"; then
    r=FAIL; why="record: $(python3 -c "import json,sys; print(json.dumps(json.load(open(sys.argv[1]))['integers']))" "$rec")"
  elif [ -n "$pat" ]; then
    case "$pat" in
      !*) if grep -q -- "${pat#!}" "$out"; then r=FAIL; why="output contains ${pat#!}"; fi ;;
      *) if ! grep -q -- "$pat" "$out"; then r=FAIL; why="output lacks $pat"; fi ;;
    esac
  fi
  if [ $r = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); fi
  printf '%s\t%s\n' "$r" "$name"
  [ -n "$why" ] && echo "    $why"
}

check c196_auto_wrap_kept \
  "i['reading'] == 'int' and i['eva'] == 'used' and i['wraps']['kept'] >= 1" __p2a_wrap_u32
check c197_auto_wrap_elided_loop \
  "i['reading'] == 'int' and i['eva'] == 'used' and i['wraps']['kept'] == 0 and len(i['wraps']['elided']) >= 1 and i['wraps']['ext_elided'] >= 1" \
  '!__p2a_wrap'
check c198_auto_recursion_fallback \
  "i['reading'] == 'int' and i['eva'] == 'fallback:recursion' and i['wraps']['kept'] >= 2 and i['wraps']['elided'] == []"
check c199_auto_bitand_bv \
  "i['reading'] == 'bv' and any(s['operation'] == '&' for s in i['bv_sites'])" '!__p2a_wrap'
check c200_auto_shift_rescued \
  "i['reading'] == 'int' and i['rescued'] >= 1"
check c201_auto_nonneg \
  "i['reading'] == 'int' and i['wraps']['nonneg'] >= 1" __p2a_wrapnn_u32
check c202_auto_large_leaf_kept \
  "i['reading'] == 'int' and i['eva'] == 'used' and i['wraps']['kept'] >= 1" __p2a_wrap_u32

echo "pass $pass fail $fail"
echo DONE
[ $fail -eq 0 ]
