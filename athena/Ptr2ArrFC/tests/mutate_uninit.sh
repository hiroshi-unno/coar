#!/bin/bash
# Is each check and each state write of an --uninit=check output needed?
# The output of ptr2arr --uninit=check on IN.c is mutated one line at a
# time, and each mutant is run against the input (tools/p2a_diff.py
# --uninit check, E-ACSL's build of the input as the reference) on SEEDS
# seeds; a mutant is killed when the run tells it apart (RESULT DIFF) or
# gives other verdicts than the output itself (a stop the reference cannot
# judge, struct-read or uninit-pattern, appearing or going away):
#   check   a call of a check (p2a_uninit_check, p2a_uninit_check_S) removed:
#           a read it guarded goes unreported (missed);
#   write   a state set to written (= 1) removed: a later read of what was
#           written is reported (false-alarm);
#   copy    a state copied from another (a structure assigned or returned
#           whole) removed, so that the destination keeps the state it had
#           (nothing written, for a fresh one): a read of a field the copy
#           carried as written is reported.
# A mutant that survives guards nothing those seeds reach (or is
# redundant): a check whose read every seed writes first, a write no seed
# reads after.
#
# usage: tests/mutate_uninit.sh WORKDIR IN.c [SEEDS] [ptr2arr options]
# Prints one line per mutant (line, kind, text, killed|survived), then the
# counts and DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
work=${1:?usage: mutate_uninit.sh WORKDIR IN.c [SEEDS] [options]}
src=${2:?usage: mutate_uninit.sh WORKDIR IN.c [SEEDS] [options]}
n=${3:-10}
shift 3 2>/dev/null || shift $#
mkdir -p "$work"
work=$(cd "$work" && pwd)
"$exe" --uninit=check "$@" -o "$work/out.c" "$src" > "$work/transform.log" 2>&1 \
  || { echo "transform failed"; exit 1; }
model=LP64; mode=normal
for o in "$@"; do
  case "$o" in
    --data-model=*) model=${o#*=} ;;
    --memory-safety|--memory-cleanup|--assume-safety) mode=${o#--} ;;
  esac
done
seeds=$(seq -s, 1 "$n")
base=$(python3 "$here/tools/p2a_diff.py" --uninit check --mode "$mode" --data-model "$model" \
         --seeds "$seeds" --workdir "$work/w_base" "$src" "$work/out.c" | tail -1)
echo "unmutated: $base"
killed=0; survived=0
mutate() {  # LINE KIND SED-EXPRESSION
  local l=$1 kind=$2 m="$work/m_$1.c"
  sed "$3" "$work/out.c" > "$m"
  cmp -s "$m" "$work/out.c" && return
  cp "$work/out.p2a.json" "$work/m_$l.p2a.json"
  local r
  r=$(python3 "$here/tools/p2a_diff.py" --uninit check --mode "$mode" --data-model "$model" \
        --seeds "$seeds" --workdir "$work/w_$l" "$src" "$m" | tail -1)
  local text v
  text=$(sed -n "${l}p" "$work/out.c" | sed 's/^ *//')
  if [ "$r" != "$base" ] || [ "${r#RESULT DIFF}" != "$r" ]; then
    v=killed; killed=$((killed + 1))
  else
    v=survived; survived=$((survived + 1))
  fi
  printf '%s\t%s\t%s\t%s\n' "$l" "$kind" "$text" "$v"
}
# a check is a call with a state argument, a write or a copy an assignment
# to a state (the generated functions' own variables have other names)
for l in $(grep -n '^ *p2a_uninit_check[A-Za-z0-9_]*([^)]*__init[^;]*);' "$work/out.c" | cut -d: -f1); do
  mutate "$l" check "${l}s/p2a_uninit_check[A-Za-z0-9_]*([^;]*);/;/"
done
for l in $(grep -n '__init[^=;]* = (unsigned char)1;' "$work/out.c" | cut -d: -f1); do
  mutate "$l" write "${l}s/(unsigned char)1;/(unsigned char)0;/"
done
for l in $(grep -n '^ *[A-Za-z_0-9]*__init[^=;]* = [A-Za-z_0-9]*__\(ret_\)\?init[^;]*;' "$work/out.c" | cut -d: -f1); do
  mutate "$l" copy "${l}s/.*/;/"
done
echo "killed=$killed survived=$survived"
echo DONE
