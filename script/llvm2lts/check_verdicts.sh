#!/usr/bin/env bash
# Translates the inputs of athena/llvm2lts/test/translate, test/arrays,
# test/structs and test/intmodes (for unreach-call) and
# athena/llvm2lts/test/termination (for termination) with llvm2lts, in each
# --mode (bv and the four Int readings), solves each T2 file with CoAR (-p
# ltssafebv / ltssafe, -p ltstermbv / ltsterm), and compares the answer with
# the one the file name states: *_true.ll must give YES (reach_error is
# unreachable; every execution terminates), *_false.ll NO, except where the
# table below says that a mode reads the program differently.  An input a mode
# refuses is listed, not counted.
#
#   script/llvm2lts/check_verdicts.sh [COAR_IMAGE]
#
# llvm2lts must be built first (script/llvm2lts/dune.sh); LLVM2LTS names
# another executable.  CoAR runs in a
# container (default image coar:svcomp, two CPUs, 4 GB; CoAR at /opt/coar, or
# at /root/coar in older images), 30 s per file.  Prints one line per file and mode, then a count and DONE; exits 1 if
# an answer differs from the expected one.
set -uo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
image=${1:-coar:svcomp}
exe=${LLVM2LTS:-$root/_build_llvm2lts/default/athena/llvm2lts/bin/main.exe}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

modes="bv int int-bitwise int-wrap-unsigned int-wrap-all"

# The answers that differ from the file name's, by design of the mode (safety
# only): NAME MODE ANSWER.  int and int-bitwise do not model wrap-around
# (unsigned 0 - 1 is -1, a trunc keeps its value, an array's arbitrary
# contents are arbitrary integers); int-wrap-all wraps signed overflow, which
# the C program and the other modes exclude.
expected_by_mode="
unsigned_wrap_true int NO
unsigned_wrap_true int-bitwise NO
conversion_true int NO
conversion_true int-bitwise NO
array_range_true int NO
array_range_true int-bitwise NO
signed_overflow_true int-wrap-all NO
nsw_true int-wrap-all NO
"

translate() {  # directory, property, tag
  for f in "$root/athena/llvm2lts/test/$1"/*.ll; do
    b=$(basename "$f" .ll)
    for m in $modes; do
      "$exe" --property "$2" --mode "$m" -o "$work/$b.$3.$m.t2" "$f" 2> "$work/$b.$3.$m.err" \
        || echo "$b $3 $m: not translated: $(tail -1 "$work/$b.$3.$m.err")" > "$work/$b.$3.$m.skip"
    done
  done
}
translate translate unreach-call safe
translate arrays unreach-call safe
translate structs unreach-call safe
translate intmodes unreach-call safe
translate termination termination term

cat > "$work/run.sh" <<'EOF'
coar=/root/coar; [ -x /opt/coar/bin/coar ] && coar=/opt/coar
export LD_LIBRARY_PATH=$coar/lib/dg:$coar/lib/apron:$coar/lib/deps
cd $coar
for f in /w/*.t2; do
  b=$(basename "$f" .t2)
  case $b in *.safe.bv) p=ltssafebv ;; *.safe.*) p=ltssafe ;; *.term.bv) p=ltstermbv ;; *) p=ltsterm ;; esac
  timeout 30 ./bin/coar -c ./config/solver/muval_yesno.json -p $p "$f" \
    > "/w/$b.out" 2> "/w/$b.coar.err"
done
EOF
docker run --rm --cpus=2 --memory=4g -v "$work":/w --entrypoint sh "$image" /w/run.sh

total=0 bad=0
for t2 in "$work"/*.t2; do
  b=$(basename "$t2" .t2) mode=${b##*.} rest=${b%.*} property=${rest##*.} name=${rest%.*}
  case $name in *_true) expected=YES ;; *_false) expected=NO ;; *) continue ;; esac
  if [ "$property" = safe ]; then
    special=$(echo "$expected_by_mode" | awk -v n="$name" -v m="$mode" '$1 == n && $2 == m { print $3 }')
    [ -n "$special" ] && expected=$special
  fi
  got=$(tail -1 "$work/$b.out" 2>/dev/null)
  total=$((total + 1))
  if [ "$got" = "$expected" ]; then
    echo "ok   $name $property $mode $got"
  else
    echo "DIFF $name $property $mode expected $expected, got ${got:-no answer}"
    bad=$((bad + 1))
  fi
done
cat "$work"/*.skip 2>/dev/null
echo "$total checked, $bad differ"
echo DONE
[ "$bad" -eq 0 ]
