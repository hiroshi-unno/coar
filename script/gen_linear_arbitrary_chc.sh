#!/bin/bash
# Regenerate SeaHorn's small-step CHC encoding of the LinearArbitrary C programs, beside the 2021 set of the same
# encoding that this repository tracked as benchmarks/CHC/LinearArbitrary (286 files, generator unrecorded; no
# SeaHorn image reproduces it).
#
# THE 2021 SET IS THE CHECK'S REFERENCE, AND MOST OF IT IS NO LONGER IN THE TREE.  Since 2026-11-03 only the files
# something cites remain, as benchmarks/CHC/LinearArbitrary_kept; the rest are in the history.  Every output is
# checked against the 2021 file of its name, so with TRACKED unset the full set is read out of commit
# LINARB_2021_COMMIT (the last commit holding all 286) into the work directory -- this needs the repository's history,
# which a shallow clone does not have.  TRACKED=DIR reads a directory instead.
#
#   script/gen_linear_arbitrary_chc.sh [OUT]   generate into OUT (default benchmarks/CHC/LinearArbitrary_regen2026,
#                                              which is ignored); script/fetch_benchmarks.sh linarb-regen runs this
#
# Needs Docker (run it on a machine where a multi-GB image may be pulled), z3 on PATH (or Z3=...) and the
# submodule benchmarks/LinearArbitrary-SeaHorn checked out.  Run from the repository root.
#
# SOURCE.  The C programs are the test programs of github.com/GaloisInc/LinearArbitrary-SeaHorn, a CHC solver built
# on SeaHorn, which is the submodule.  script/fetch/linarb-regen.mapping maps each tracked
# file name to the upstream path(s) with the same basename; a name whose basename occurs in several directories
# (01.c is in three) is generated once per candidate path, so OUT mirrors the upstream tree and the mapping, not a
# guess, says which file stands for a tracked name.
#
# WHAT IS RUN, per program, in the image SeaHorn publishes (pinned by digest, IMAGE):
#   sea smt --step=small --horn-format=pure-smt2 $SEA_FLAGS -o <p>.small.smt2 <p>
# SEA_FLAGS defaults to --ignore-define-verifier-fns=true.  Without it, a program that *defines*
# __VERIFIER_assert (void __VERIFIER_assert(int c) { if (!c) __VERIFIER_error(); }) has its calls turned into
# SeaHorn's verifier.assert, which this small-step encoder does not encode: SeaHorn warns "no assertion was
# found" and writes a trivially satisfiable system, which is wrong for every unsafe program.  With the flag the
# defined function is compiled as ordinary code calling the undefined __VERIFIER_error, the error SeaHorn does
# encode.
#
# THE GENERATION-TIME PATCH.  Many programs take their nondeterminism from a one-line definition reading an
# uninitialised local, such as int unknown(){int x; return x;} -- undefined behaviour, which an optimiser may fold
# to a constant.  Every such definition, int NAME(PARAMS){int V; return V;} on one line, is replaced by the
# external declaration extern int NAME(PARAMS); before SeaHorn sees the file, so the value is a genuine unknown.
# The manifest records the sha256 of the upstream file and of the patched input.
#
# THE CHECKS, per output, after which only accepted files are placed in OUT:
#   failed                     SeaHorn exited non-zero (or by SEA_TIMEOUT) or wrote nothing
#   rejected-no-assertion      its log says "no assertion was found": the encoding lost the property
#   rejected-contradicts-label z3 (Z3_TIMEOUT s) decides it against the verdict in the program's name
#   rejected-contradicts-tracked  z3 decides it and the tracked file oppositely
#   accepted                   otherwise (including when z3 decides neither, or only one side)
# The label is read from the tracked name: unsafe, false-unreach-call or VeriMAP_false mean unsat (the error is
# reachable), safe, ok, true-unreach-call or VeriMAP_true mean sat; other names carry none.  A rejected
# contradiction is not proof that SeaHorn erred -- for a name with several candidate paths it can mean that this
# candidate is not the program the tracked file came from -- so it is reported, not shipped.
#
# THE MANIFEST, OUT/MANIFEST.tsv: '#' lines give the image and its digest, the SeaHorn version string, the
# command, the patch, the date, the submodule commit, the z3 version and the counts; then one line per candidate:
#   upstream_path  tracked_name  status  label  tracked_verdict  regen_verdict  sha256_upstream  sha256_input  sha256_output  output
# (verdicts sat, unsat or none; sha256_output is that of SeaHorn's output, placed or not, '-' when there is none;
# output is '-' when nothing was placed).  SeaHorn writes the temporary bitcode path into (set-info :original ...);
# it is replaced by the upstream path, which leaves the output a function of the input and the image: two runs
# wrote the same files byte for byte.
#
# THE PIN, script/fetch/linarb-regen.pinned (PINNED=...), tracked: one line per SeaHorn output of the pinned image,
#   upstream_path <TAB> sha256_output
# placed or rejected alike, so that it does not depend on z3's budget.  After generating, every candidate whose
# output differs from the pin, is missing although pinned, or exists although not pinned is reported, and the
# script exits with status 3 (the files are still placed, and the manifest says which differ).  A pin is written
# from a run's manifest with PIN_WRITE=FILE; a new pin is a decision, made only when the image or the inputs change
# on purpose.
set -u

OUT=${1:-benchmarks/CHC/LinearArbitrary_regen2026}
SUB=${SUB:-benchmarks/LinearArbitrary-SeaHorn}
TRACKED=${TRACKED:-}
TRACKED_DESC=$TRACKED
LINARB_2021_COMMIT=${LINARB_2021_COMMIT:-5f1b742f172e6cb29a10f87f32217e0b3fcfea79}
MAPPING=${MAPPING:-script/fetch/linarb-regen.mapping}
IMAGE=${IMAGE:-seahorn/seahorn-llvm14@sha256:aace262a5ee8c8bc6288e6fdf772792e1362e8d5fde3172906647e75f92bf5fb}
DOCKER=${DOCKER:-docker}
Z3=${Z3:-z3}
Z3_TIMEOUT=${Z3_TIMEOUT:-10}
SEA_TIMEOUT=${SEA_TIMEOUT:-120}
SEA_FLAGS=${SEA_FLAGS---ignore-define-verifier-fns=true}
JOBS=${JOBS:-2}
PINNED=${PINNED:-script/fetch/linarb-regen.pinned}
SED_PATCH='s/^([[:space:]]*)int[[:space:]]+([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*(\([^)]*\))[[:space:]]*\{[[:space:]]*int[[:space:]]+([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*;[[:space:]]*return[[:space:]]+\4[[:space:]]*;[[:space:]]*\}/\1extern int \2\3;/'

die() { echo "gen_linear_arbitrary_chc: $*" >&2; exit 1; }
for t in sha256sum timeout; do command -v $t >/dev/null || die "$t is needed"; done
$DOCKER version >/dev/null 2>&1 || die "Docker is needed (DOCKER='$DOCKER' does not answer)"
command -v "$Z3" >/dev/null || die "z3 is needed (Z3=$Z3)"
[ -f "$MAPPING" ] || die "no mapping $MAPPING (run from the repository root)"
[ -z "$TRACKED" ] || [ -d "$TRACKED" ] || die "no tracked set $TRACKED"
[ -f "$SUB/README.md" ] || die "the submodule $SUB is not checked out"
if [ -d "$OUT" ] && [ -n "$(ls -A "$OUT" 2>/dev/null)" ]; then die "$OUT is not empty"; fi

W=$(mktemp -d "${TMPDIR:-/tmp}/linarb_regen.XXXXXX") || exit 1
# KEEP_WORK=1 keeps the work directory (inputs, every output and SeaHorn's logs) for inspection.
if [ -n "${KEEP_WORK:-}" ]; then echo "work directory: $W"; else trap 'rm -rf "$W"' EXIT; fi
mkdir -p "$W/in" "$W/out" && chmod 777 "$W" "$W/in" "$W/out"
if [ -z "$TRACKED" ]; then
  mkdir -p "$W/tracked2021" || exit 1
  git archive "$LINARB_2021_COMMIT" benchmarks/CHC/LinearArbitrary | tar -x -C "$W/tracked2021" \
    || die "cannot read the 2021 set from commit $LINARB_2021_COMMIT (a shallow clone lacks it; TRACKED=DIR reads a directory)"
  TRACKED="$W/tracked2021/benchmarks/CHC/LinearArbitrary"
  TRACKED_DESC="benchmarks/CHC/LinearArbitrary at $LINARB_2021_COMMIT"
  [ "$(ls "$TRACKED" | wc -l)" -eq 286 ] || die "commit $LINARB_2021_COMMIT gave $(ls "$TRACKED" | wc -l) files, not 286"
fi

# candidate paths, each with its tracked name
grep -v '^#' "$MAPPING" | awk -F'\t' '$3 != "" && $3 != "-" { n = split($3, a, ";"); for (i = 1; i <= n; i++) print a[i] "\t" $1 }' \
  | LC_ALL=C sort -u > "$W/cands.tsv"
cut -f1 "$W/cands.tsv" > "$W/list"
echo "candidates: $(wc -l < "$W/list") upstream paths for $(cut -f2 "$W/cands.tsv" | sort -u | wc -l) tracked names"

while IFS=$'\t' read -r p _; do
  [ -f "$SUB/$p" ] || die "missing upstream file $SUB/$p (is the submodule at the pinned commit?)"
  mkdir -p "$W/in/$(dirname "$p")" "$W/out/$(dirname "$p")"
  sed -E "$SED_PATCH" "$SUB/$p" > "$W/in/$p"
done < "$W/cands.tsv"
chmod -R a+rwX "$W/in" "$W/out"

echo "pulling $IMAGE"
$DOCKER pull -q "$IMAGE" >/dev/null || die "cannot pull $IMAGE"
created=$($DOCKER inspect --format '{{.Created}}' "$IMAGE")
seaver=$($DOCKER run --rm "$IMAGE" sh -c 'echo "int main(){return 0;}" > /tmp/v.c && cd /tmp && sea smt --step=small --horn-format=pure-smt2 -o v.smt2 v.c >/dev/null 2>&1; sed -n "s/.*:authors \"\(.*\)\").*/\1/p" v.smt2')

echo "running SeaHorn on $(wc -l < "$W/list") programs"
$DOCKER run --rm -v "$W:/w" -e SEA_FLAGS="$SEA_FLAGS" -e SEA_TIMEOUT="$SEA_TIMEOUT" "$IMAGE" sh -c '
  while read p; do
    d=$(dirname "$p"); b=$(basename "$p")
    (cd "/w/in/$d" && timeout "$SEA_TIMEOUT" sea smt --step=small --horn-format=pure-smt2 $SEA_FLAGS \
       -o "/w/out/$p.small.smt2" "$b" > "/w/out/$p.log" 2>&1)
    printf "%s\t%s\n" "$p" "$?"
  done < /w/list' > "$W/rc.tsv"
[ "$(wc -l < "$W/rc.tsv")" -eq "$(wc -l < "$W/list")" ] || die "SeaHorn's loop stopped early: $(wc -l < "$W/rc.tsv") of $(wc -l < "$W/list")"

# the temporary bitcode path SeaHorn records becomes the upstream path
while IFS=$'\t' read -r p rc; do
  f="$W/out/$p.small.smt2"
  [ -s "$f" ] && sed -i "s|^(set-info :original \".*\")\$|(set-info :original \"$p\")|" "$f"
done < "$W/rc.tsv"

# z3 verdicts: the tracked files and the outputs
z3v() { local r; r=$(timeout "$Z3_TIMEOUT" "$Z3" "$1" 2>/dev/null | head -1); case $r in sat|unsat) echo "$r" ;; *) echo none ;; esac; }
export -f z3v; export Z3 Z3_TIMEOUT
echo "checking with $("$Z3" --version), ${Z3_TIMEOUT}s per file, $JOBS at a time"
cut -f2 "$W/cands.tsv" | LC_ALL=C sort -u | xargs -P "$JOBS" -I{} bash -c 'printf "%s\t%s\n" "{}" "$(z3v "'"$TRACKED"'/{}")"' > "$W/tracked.tsv"
awk -F'\t' '$2 == 0 { print $1 }' "$W/rc.tsv" | while read -r p; do [ -s "$W/out/$p.small.smt2" ] && echo "$p"; done \
  | xargs -P "$JOBS" -I{} bash -c 'printf "%s\t%s\n" "{}" "$(z3v "'"$W"'/out/{}.small.smt2")"' > "$W/regen.tsv"

label_of() {
  case $1 in
  *unsafe* | *false-unreach-call* | *VeriMAP_false*) echo unsat ;;
  *true-unreach-call* | *VeriMAP_true* | *_safe.* | *-safe.* | *_ok.* | *-ok.* | *-ok[0-9].*) echo sat ;;
  *) echo none ;;
  esac
}

mkdir -p "$OUT" || exit 1
M="$OUT/MANIFEST.tsv"
body="$W/manifest_body.tsv"
: > "$body"
while IFS=$'\t' read -r p name; do
  rc=$(awk -F'\t' -v p="$p" '$1 == p { print $2 }' "$W/rc.tsv")
  lab=$(label_of "$name")
  tv=$(awk -F'\t' -v n="$name" '$1 == n { print $2 }' "$W/tracked.tsv")
  rv=$(awk -F'\t' -v p="$p" '$1 == p { print $2 }' "$W/regen.tsv"); rv=${rv:-none}
  f="$W/out/$p.small.smt2"
  if [ "$rc" != 0 ] || [ ! -s "$f" ]; then st=failed
  elif grep -q 'no assertion was found' "$W/out/$p.log"; then st=rejected-no-assertion
  elif [ "$lab" != none ] && [ "$rv" != none ] && [ "$rv" != "$lab" ]; then st=rejected-contradicts-label
  elif [ "$tv" != none ] && [ "$rv" != none ] && [ "$rv" != "$tv" ]; then st=rejected-contradicts-tracked
  else st=accepted; fi
  su=$(sha256sum < "$SUB/$p" | cut -d' ' -f1)
  si=$(sha256sum < "$W/in/$p" | cut -d' ' -f1)
  so=-; o=-
  [ -s "$f" ] && so=$(sha256sum < "$f" | cut -d' ' -f1)
  if [ $st = accepted ]; then
    o="$p.small.smt2"; mkdir -p "$OUT/$(dirname "$p")" && cp "$f" "$OUT/$o" || die "cannot place $o"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$p" "$name" "$st" "$lab" "$tv" "$rv" "$su" "$si" "$so" "$o" >> "$body"
done < "$W/cands.tsv"

{
  echo "# LinearArbitrary C programs regenerated as SeaHorn small-step CHC (script/gen_linear_arbitrary_chc.sh)"
  echo "# date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# image: $IMAGE"
  echo "# image created: $created"
  echo "# seahorn: ${seaver:-unknown}"
  echo "# command: sea smt --step=small --horn-format=pure-smt2 $SEA_FLAGS -o <path>.small.smt2 <path>   (timeout ${SEA_TIMEOUT}s, run in the program's directory)"
  echo "# patch: sed -E '$SED_PATCH'"
  echo "# submodule: $SUB at $(git -C "$SUB" rev-parse HEAD 2>/dev/null || echo unknown) (https://github.com/GaloisInc/LinearArbitrary-SeaHorn)"
  echo "# check: $("$Z3" --version), ${Z3_TIMEOUT}s per file, against $TRACKED_DESC and the label in the tracked name"
  echo "# counts: $(cut -f3 "$body" | sort | uniq -c | awk '{printf "%s%s %s", (NR>1?", ":""), $2, $1}')"
  echo "# upstream_path	tracked_name	status	label	tracked_verdict	regen_verdict	sha256_upstream	sha256_input	sha256_output	output"
  cat "$body"
} > "$M"
echo "$OUT: $(grep -c $'\taccepted\t' "$M") files placed; $(grep '^# counts' "$M" | cut -c3-)"

if [ -n "${PIN_WRITE:-}" ]; then
  { echo "# SeaHorn outputs of script/gen_linear_arbitrary_chc.sh, pinned: upstream_path<TAB>sha256 of the output"
    echo "# from the run of $(sed -n 's/^# date: //p' "$M"), $IMAGE, SEA_FLAGS=$SEA_FLAGS"
    awk -F'\t' '$9 != "-" { print $1 "\t" $9 }' "$body"; } > "$PIN_WRITE"
  echo "wrote the pin $PIN_WRITE ($(grep -vc '^#' "$PIN_WRITE") outputs)"
fi
if [ -f "$PINNED" ]; then
  diffs=$(join -t $'\t' -a1 -a2 -e - -o 0,1.2,2.2 \
            <(grep -v '^#' "$PINNED" | LC_ALL=C sort) \
            <(awk -F'\t' '$9 != "-" { print $1 "\t" $9 }' "$body" | LC_ALL=C sort) | awk -F'\t' '$2 != $3')
  if [ -n "$diffs" ]; then
    echo "DIFFERS FROM THE PIN $PINNED ($(printf '%s\n' "$diffs" | wc -l) files; pinned, this run):"
    printf '%s\n' "$diffs" | awk -F'\t' '{ print "  " $1 "  " $2 "  " $3 }'
    exit 3
  fi
  echo "every output matches the pin $PINNED ($(grep -vc '^#' "$PINNED") files)"
else
  echo "no pin at $PINNED: outputs not compared"
fi
