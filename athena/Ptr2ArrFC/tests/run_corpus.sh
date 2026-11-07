#!/bin/bash
# Totality run over a corpus: transform, check and compile each file, without
# running anything (for the differential run see tests/run_tests.sh).
#
# usage: tests/run_corpus.sh LIST OUTDIR [JOBS] [TIMEOUT]
#   LIST     a file with one C file per line (absolute, or relative to the
#            repository root)
#   JOBS     files processed in parallel (default 3)
#   TIMEOUT  seconds allowed for each transformation (default 60)
#
# OUTDIR/summary.tsv has one line per file: name, transform status (0
# written, 1 unreadable or not implemented, 2 unsupported, 124 timeout),
# check status, compile status (gcc -c on the output), and the reason of a
# refusal (the first unsupported construct's kind, or the not-implemented
# message). The script ends with the counts and the line DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/../.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
list=${1:?usage: run_corpus.sh LIST OUTDIR [JOBS] [TIMEOUT]}
out=${2:?usage: run_corpus.sh LIST OUTDIR [JOBS] [TIMEOUT]}
jobs=${3:-3}
tmo=${4:-60}
mkdir -p "$out"
out=$(cd "$out" && pwd)
[ -x "$exe" ] || { echo "missing $exe"; exit 1; }

one() {
  src=$1
  case $src in /*) ;; *) src="$repo/$src" ;; esac
  name=$(echo "${src#$repo/}" | tr '/' '_' | sed 's/\.c$//')
  d="$out/files/$name"
  rm -rf "$d"; mkdir -p "$d"
  timeout "$tmo" "$exe" -o "$d/out.c" "$src" > "$d/transform.log" 2>&1
  t=$?
  c=-; g=-; why=-
  if [ $t -eq 0 ]; then
    "$exe" --check "$d/out.c" > "$d/check.log" 2>&1; c=$?
    gcc -c -w -std=gnu11 "$d/out.c" -o "$d/out.o" > "$d/gcc.log" 2>&1; g=$?
  elif [ $t -eq 2 ]; then
    why=$(grep -m1 '^ptr2arr: unsupported:' "$d/transform.log" \
          | sed 's/^ptr2arr: unsupported: //; s/^[^ ]*: \([a-z-]*\):.*/\1/' | cut -c1-60)
  elif [ $t -eq 1 ]; then
    why=$(grep -m1 -o 'not implemented yet: .*' "$d/transform.log" | cut -c1-80)
    [ -n "$why" ] || why=$(grep -m1 -E 'User Error|Error|aborted' "$d/transform.log" | cut -c1-80)
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$t" "$c" "$g" "${why:--}"
}
export -f one
export exe out repo tmo

grep -v '^\s*$' "$list" | xargs -P "$jobs" -I{} bash -c 'one "$@"' _ {} > "$out/rows.tsv"
{ printf 'name\ttransform\tcheck\tcompile\treason\n'; sort "$out/rows.tsv"; } > "$out/summary.tsv"
for col in 2 3 4; do
  echo "== $(head -1 "$out/summary.tsv" | cut -f$col)"
  tail -n +2 "$out/summary.tsv" | cut -f$col | sort | uniq -c
done
echo "== reasons (transform 1 or 2)"
tail -n +2 "$out/summary.tsv" | awk -F'\t' '$2==1||$2==2{print $2" "$5}' | sort | uniq -c | sort -rn | head -40
echo "files: $(($(wc -l < "$out/summary.tsv") - 1))"
echo DONE
