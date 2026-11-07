#!/bin/bash
# The check functions of ptr2arr --check-overflow tested against a reference
# (tests/overflow_conds.c), in both data models.
# usage: tests/overflow_conds.sh WORKDIR ; ends with one "MODEL ok|FAIL" line
# per data model and DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
work=${1:?usage: overflow_conds.sh WORKDIR}
mkdir -p "$work"
for model in LP64 ILP32; do
  m=; [ "$model" = ILP32 ] && m=-m32
  "$exe" --check-overflow --data-model=$model -o "$work/out_$model.c" \
    "$here/tests/overflow_conds_ops.c" > "$work/transform_$model.log" 2>&1 \
    || { echo "$model transform-fail"; continue; }
  gcc -O0 -w $m -Dmain=p2a_unused_main -c "$work/out_$model.c" -o "$work/out_$model.o" \
    && gcc -O0 -w $m "$here/tests/overflow_conds.c" "$work/out_$model.o" -o "$work/conds_$model" \
    || { echo "$model compile-fail"; continue; }
  if "$work/conds_$model" > "$work/conds_$model.log" 2>&1; then echo "$model ok"
  else echo "$model FAIL"; fi
  cat "$work/conds_$model.log"
done
echo DONE
