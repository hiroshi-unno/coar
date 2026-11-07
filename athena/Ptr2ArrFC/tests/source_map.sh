#!/bin/bash
# The source map of the record (source_map), checked on every test input.
#
# usage: tests/source_map.sh [--diff] OUTDIR [input ...]
#   (default inputs: tests/cases/*.c, tests/cases/*.i and the files named in
#    tests/bench.list)
#
# 1. expect: each section of tests/source_map.expect (an input under
#    tests/cases and options) is transformed and its map must hold the
#    entries the section lists (tools/p2a_srcmap_check.py --expect).
# 2. check: every input is transformed in each configuration below, with
#    and without --line-directives, and tools/p2a_srcmap_check.py checks
#    every entry against the output and the input (an output position on
#    the first character of a statement, printed as its role says; an input
#    position on a token, a target's on a statement or full expression; with
#    --line-directives, the #line line above each statement naming its
#    input line). An output written with --line-directives must also
#    compile (gcc -fsyntax-only), pass ptr2arr --check, and, read without
#    its #line lines and whitespace aside, be the output written without
#    the option.
# 3. with --diff: tools/p2a_diff.py runs every output written with
#    --line-directives in the normal mode against its input.
#
# One line per failure; the script ends with the counts and the line DONE,
# and exits 1 if anything failed.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/../.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
check="$here/tools/p2a_srcmap_check.py"
[ -x "$exe" ] || { echo "missing $exe; build with: dune build --root $here"; exit 1; }
diff_run=
if [ "${1:-}" = --diff ]; then diff_run=1; shift; fi
out=${1:?usage: source_map.sh [--diff] OUTDIR [input ...]}
shift
mkdir -p "$out"
out=$(cd "$out" && pwd)

inputs=("$@")
if [ ${#inputs[@]} -eq 0 ]; then
  inputs=("$here"/tests/cases/*.c "$here"/tests/cases/*.i)
  while read -r f; do inputs+=("$repo/$f"); done < "$here/tests/bench.list"
fi

configs=("" "--memory-safety" "--memory-safety --violation-markers=reach-error"
  "--memory-safety --memtrack-nonterminating" "--memory-cleanup" "--assume-safety"
  "--check-overflow" "--wrap-integers" "--data-model=ILP32" "--data-model=ILP32 --memory-safety"
  "--identity" "--monitor")

pass=0; fail=0; refused=0
bad() { fail=$((fail + 1)); echo "FAIL $*"; }

echo "== expect"
section=; opts=(); exp=
flush() {
  [ -n "$section" ] || return
  local d="$out/expect/$(echo "$section ${opts[*]}" | tr ' =/' '___')"
  mkdir -p "$d"
  if ! (cd "$d" && "$exe" "${opts[@]}" -o out.c "$here/tests/cases/$section") > "$d/transform.log" 2>&1; then
    bad "expect $section ${opts[*]}: transform failed"
  elif python3 "$check" --expect "$exp" "$here/tests/cases/$section" "$d/out.c" "$d/out.p2a.json" \
         > "$d/check.log" 2>&1; then
    pass=$((pass + 1))
  else
    bad "expect $section ${opts[*]}"; grep -v '^FAIL' "$d/check.log" | sed 's/^/    /'
  fi
}
mkdir -p "$out/expect"
while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in
    "== "*)
      flush
      read -r -a words <<< "${line#== }"
      section=${words[0]}; opts=("${words[@]:1}")
      exp="$out/expect/$(echo "$section ${opts[*]}" | tr ' =/' '___').expect"
      : > "$exp" ;;
    *) [ -n "$section" ] && printf '%s\n' "$line" >> "$exp" ;;
  esac
done < "$here/tests/source_map.expect"
flush

echo "== check"
declare -A seen
for src in "${inputs[@]}"; do
  name=$(basename "$src"); name=${name%.*}
  base=$name; k=1
  while [ -n "${seen[$name]:-}" ]; do k=$((k + 1)); name="${base}_$k"; done
  seen[$name]=1
  for ci in "${!configs[@]}"; do
    read -r -a cfg <<< "${configs[$ci]}"
    d="$out/check/$name/$ci"; mkdir -p "$d"
    m32=(); case " ${cfg[*]} " in *ILP32*) m32=(-m32) ;; esac
    chk=(); dm=()
    for a in "${cfg[@]}"; do
      case "$a" in --identity|--monitor) chk=(--allow-pointers) ;; --data-model=*) dm=("$a") ;; esac
    done
    if ! "$exe" "${cfg[@]}" -o "$d/out.c" "$src" > "$d/out.log" 2>&1; then
      refused=$((refused + 1)); continue
    fi
    for v in out lines; do
      if [ $v = lines ]; then
        if ! "$exe" "${cfg[@]}" --line-directives -o "$d/lines.c" "$src" > "$d/lines.log" 2>&1; then
          bad "$name [${configs[$ci]}] --line-directives: transform failed"; continue
        fi
      fi
      if python3 "$check" "$src" "$d/$v.c" "$d/$v.p2a.json" > "$d/$v.check" 2>&1; then
        pass=$((pass + 1))
      else
        bad "$name [${configs[$ci]}] $v"; grep -v '^FAIL' "$d/$v.check" | head -5 | sed 's/^/    /'
      fi
    done
    [ -f "$d/lines.c" ] || continue
    # the #line lines (each on a line of its own, the line it splits
    # indented again) are all the option changes in the program
    if ! grep -v '^#line ' "$d/lines.c" | tr -s ' \t\n' ' ' | cmp -s - <(tr -s ' \t\n' ' ' < "$d/out.c"); then
      bad "$name [${configs[$ci]}]: --line-directives changes more than #line lines"
    fi
    if ! gcc -fsyntax-only -w "${m32[@]}" "$d/lines.c" > "$d/gcc.log" 2>&1; then
      bad "$name [${configs[$ci]}]: the --line-directives output does not compile"
    fi
    if ! "$exe" --check "${chk[@]}" "${dm[@]}" "$d/lines.c" > "$d/pcheck.log" 2>&1; then
      bad "$name [${configs[$ci]}]: ptr2arr --check refuses the --line-directives output"
    fi
    if [ -n "$diff_run" ] && [ -z "${configs[$ci]}" ]; then
      python3 "$here/tools/p2a_diff.py" --workdir "$d/diff" "$src" "$d/lines.c" > "$d/diff.log" 2>&1
      r=$(grep '^RESULT' "$d/diff.log" | awk '{print $2}')
      echo "diff $name ${r:-error}" >> "$out/diff.tsv"
    fi
  done
done
[ -f "$out/diff.tsv" ] && { echo "== p2a_diff on the --line-directives outputs"; awk '{print $3}' "$out/diff.tsv" | sort | uniq -c; }
echo "pass=$pass fail=$fail refused=$refused"
echo DONE
[ $fail -eq 0 ]
