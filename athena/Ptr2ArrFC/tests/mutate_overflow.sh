#!/bin/bash
# Is each overflow check of an output needed? For every call of a check
# function in the output of ptr2arr --check-overflow on IN.c, the output
# without that call is run against the input (tools/p2a_diff.py
# --check-overflow, the normalised input as the oracle) on SEEDS seeds: a
# check whose removal makes some seed differ is killed. A check that
# survives is never the first overflow of those seeds (or is redundant).
#
# usage: tests/mutate_overflow.sh WORKDIR IN.c [SEEDS] [ptr2arr options]
# Prints one line per check (line, call, killed|survived), then the counts
# and DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
work=${1:?usage: mutate_overflow.sh WORKDIR IN.c [SEEDS] [options]}
src=${2:?usage: mutate_overflow.sh WORKDIR IN.c [SEEDS] [options]}
n=${3:-40}
shift 3 2>/dev/null || shift $#
mkdir -p "$work"
"$exe" --check-overflow "$@" -o "$work/out.c" "$src" > "$work/transform.log" 2>&1 \
  || { echo "transform failed"; exit 1; }
"$exe" --identity "$@" -o "$work/ident.c" "$src" > "$work/ident.log" 2>&1 \
  || { echo "identity failed"; exit 1; }
model=LP64
for o in "$@"; do case "$o" in --data-model=*) model=${o#*=} ;; esac; done
seeds=$(seq -s, 1 "$n")
killed=0; survived=0
for l in $(grep -n '^ *\(case [^:]*: \)\?__p2a_overflow_[a-z0-9_]*(' "$work/out.c" | cut -d: -f1); do
  m="$work/m_$l.c"
  sed "${l}s/__p2a_overflow_[a-z0-9_]*([^;]*);/;/" "$work/out.c" > "$m"
  r=$(python3 "$here/tools/p2a_diff.py" --check-overflow --data-model "$model" \
        --sanitize-source "$work/ident.c" --seeds "$seeds" --workdir "$work/w_$l" \
        "$src" "$m" | tail -1)
  call=$(sed -n "${l}p" "$work/out.c" | sed 's/^ *//')
  case "$r" in
    "RESULT DIFF"*) v=killed; killed=$((killed + 1)) ;;
    *) v=survived; survived=$((survived + 1)) ;;
  esac
  printf '%s\t%s\t%s\n' "$l" "$call" "$v"
done
echo "killed=$killed survived=$survived"
echo DONE
