#!/bin/bash
# Generate the muCLP (`.hes`) instances of the SPROUT global-protocol benchmarks without solving them.
#
#   script/gen_sprout_hes.sh --build DIR     build the patched generator in DIR (outside this tree)
#   script/gen_sprout_hes.sh [OUT]           generate every Table 2 protocol's instances into OUT
#                                            (default benchmarks/sprout-generated, which is ignored)
#
# SOURCE.  SPROUT (Li, Stutz, Wies, Zufferey, CAV 2025) reduces the implementability of a symbolic
# multiparty protocol to muCLP validity.  Its protocols and its query generator are the submodule
# benchmarks/sprout (github.com/nyu-acsys/sprout, Apache-2.0); this tree stores none of their files.
# The generator writes the instances and then runs MuVal on each, interleaved in one program, so
# script/fetch/sprout-generate-only.patch adds a mode `--generate-only FILE VERSION` that writes the
# instances and calls no solver.  The patch is applied to a copy of the submodule's files, never to
# the submodule.
#
# WHAT IS GENERATED, AND WHAT THE ANSWER SHOULD BE.  Per protocol P, two directories:
#   P-generated-gclts/   the GCLTS-eligibility conditions; the protocol is eligible iff every one is
#                        `invalid`, and every Table 2 protocol is eligible;
#   P-generated/         the implementability (coherence) conditions, only for a non-binary protocol
#                        that passes the syntactic checks; implementable iff every one is `invalid`,
#                        not implementable iff some one is `valid`.
# A binary protocol (two participants) is implementable without any instance.  The ground truth per
# protocol is script/fetch/sprout.expected (Table 2's Impl. column).  OUT/instances.tsv lists every
# instance with its protocol, its kind and its expected answer (`invalid`, or `some-valid` for an
# implementability instance of a non-implementable protocol: the paper names no single one).
#
# VERSION is SPROUT's `opt` mode, the one its Table 2 evaluation runs (verify_all.sh: `40 opt
# parallel`); SPROUT_VERSION overrides it.  SPROUT_GEN names the generator binary (default: the link
# sprout-gen at the repository root, made by `ln -s DIR/query-generator/_build/default/main.exe sprout-gen`
# after --build DIR).  OPAM_SWITCH (default 5.3.0) is the switch --build uses; it needs dune, menhir,
# logs, fmt, sexplib and the ppx_compare/hash/sexp_conv/custom_printf rewriters.
set -u
cd "$(dirname "$0")/.." || exit 2
ROOT=$(pwd)
SUB=$ROOT/benchmarks/sprout
PATCH=$ROOT/script/fetch/sprout-generate-only.patch
EXPECTED=$ROOT/script/fetch/sprout.expected
GEN=${SPROUT_GEN:-$ROOT/sprout-gen}
VERSION=${SPROUT_VERSION:-opt}

if [ "${1:-}" = --build ]; then
  DIR=${2:?usage: $0 --build DIR}
  [ -e "$DIR" ] && { echo "refusing: $DIR exists" >&2; exit 2; }
  [ -f "$SUB/query-generator/main.ml" ] || { echo "benchmarks/sprout is not checked out" >&2; exit 2; }
  mkdir -p "$DIR" || exit 2
  git -C "$SUB" archive HEAD | tar -x -C "$DIR" || exit 2
  echo "nyu-acsys/sprout $(git -C "$SUB" rev-parse HEAD)" > "$DIR/SOURCE_COMMIT"
  ( cd "$DIR" && patch -p1 < "$PATCH" ) || exit 2
  ( cd "$DIR/query-generator" && opam exec --switch="${OPAM_SWITCH:-5.3.0}" -- dune build ./main.exe ) || exit 1
  echo "built $DIR/query-generator/_build/default/main.exe (link it as $ROOT/sprout-gen, or set SPROUT_GEN)"
  exit 0
fi

OUT=${1:-benchmarks/sprout-generated}
[ -x "$GEN" ] || { echo "no generator at $GEN (run $0 --build DIR and link it as sprout-gen, or set SPROUT_GEN)" >&2; exit 2; }
[ -e "$OUT" ] && { echo "refusing: $OUT exists" >&2; exit 2; }
mkdir -p "$OUT" || exit 2
OUT=$(cd "$OUT" && pwd)
"$GEN" --version > "$OUT/GENERATOR" 2>&1
printf 'instance\tprotocol\tkind\texpected\n' > "$OUT/instances.tsv"
: > "$OUT/protocols.tsv"
grep -v '^#' "$EXPECTED" | while IFS=$'\t' read -r p row parties impl; do
  cp "$SUB/examples/sprout/$p" "$OUT/$p" || { echo "FAIL $p: no protocol file"; continue; }
  # The generator names its output directories after its argument relative to its working directory.
  line=$(cd "$OUT" && "$GEN" --generate-only "$p" "$VERSION" 2> "$OUT/$p.stderr" | grep '^SPROUT-GEN')
  [ -s "$OUT/$p.stderr" ] || rm -f "$OUT/$p.stderr"
  [ -n "$line" ] || { echo "FAIL $p: generator printed no SPROUT-GEN line"; continue; }
  ng=0; ni=0
  for f in "$OUT/$p-generated-gclts"/*.hes; do
    [ -e "$f" ] || continue; ng=$((ng+1))
    printf '%s\t%s\tgclts\tinvalid\n' "${f#$ROOT/}" "$p" >> "$OUT/instances.tsv"
  done
  for f in "$OUT/$p-generated"/*.hes; do
    [ -e "$f" ] || continue; ni=$((ni+1))
    if [ "$impl" = Y ]; then e=invalid; else e=some-valid; fi
    printf '%s\t%s\timpl\t%s\n' "${f#$ROOT/}" "$p" "$e" >> "$OUT/instances.tsv"
  done
  printf '%s\t%s\t%s\t%s\tgclts=%d\timpl=%d\t%s\n' "$p" "$row" "$parties" "$impl" "$ng" "$ni" "${line#SPROUT-GEN }" \
    >> "$OUT/protocols.tsv"
done
n=$(($(wc -l < "$OUT/instances.tsv") - 1))
echo "generated $n instances for $(wc -l < "$OUT/protocols.tsv") protocols into $OUT"
echo DONE
