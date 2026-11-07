#!/bin/bash
# Generate the muCLP (`.hes`) instances of the Sprout(A) benchmarks, per protocol and network, without solving.
#
#   script/gen_sprouta_hes.sh --build DIR     build the patched generator in DIR (outside this tree)
#   script/gen_sprouta_hes.sh [OUT]           generate every Table 1 protocol's instances for the five
#                                             networks into OUT (default benchmarks/sprouta-generated,
#                                             which is ignored)
#
# SOURCE.  Sprout(A) (PLDI 2026 artifact, Zenodo record 19600644, CC-BY-4.0) extends SPROUT (CAV 2025) from
# peer-to-peer FIFO channels to five network architectures and reduces a symbolic multiparty protocol's
# implementability under each to muCLP validity.  The record holds the generator's sources (source.zip) and a
# Docker image; the protocols exist only inside the image, and script/fetch_benchmarks.sh sprouta streams them
# into the ignored benchmarks/sprouta/ without storing the image.  This tree stores none of their files.
# The generator writes the instances and runs MuVal on each in one program, so
# script/fetch/sprouta-generate-only.patch adds `--generate-only FILE NETWORK VERSION`, which writes the
# instances, calls no solver and prints one SPROUT-GEN line, and `--version`.
#
# WHAT IS GENERATED, AND WHAT THE ANSWER SHOULD BE.  Per protocol P:
#   OUT/gclts/P-generated-gclts/   the GCLTS-eligibility conditions (det, df); they do not depend on the
#                                  network (checked: each network's copy is compared with the first and
#                                  then removed).  Every Table 1 protocol is GCLTS-eligible (the README:
#                                  non-GCLTS is "not applicable to this artifact evaluation"), so each is
#                                  `invalid`;
#   OUT/NET/P-generated/           the implementability conditions under network NET (send coherence,
#                                  the network's receive coherence, no mixed choice, and for mailbox and
#                                  monobox prefix extensibility), only when the syntactic checks pass and the
#                                  protocol is not binary, a binary protocol being implementable without any
#                                  instance under every network but bag (Sprout(A)'s check_implementability).
#                                  Implementable under NET iff every one is `invalid`.
# OUT/instances.tsv lists every instance with its protocol, network, kind and expected answer: `invalid`,
# `some-valid` for an implementability instance of a protocol not implementable under that network (no
# single instance is named), or `unknown` where script/fetch/sprouta.expected has `?`.
# OUT/protocols.tsv has one line per protocol and network with the counts and the SPROUT-GEN line.
#
# VERSION is Sprout(A)'s `opt` mode, the one its Table 1 evaluation runs (verify_all.sh:
# `main.exe FILE NETWORK 30 opt parallel`); SPROUTA_VERSION overrides it.  SPROUTA_GEN names the generator
# (default: the link sprouta-gen at the repository root).  OPAM_SWITCH (default 5.3.0) is the switch --build
# uses; it needs dune, menhir, logs, fmt, sexplib, stdio and the ppx_compare/hash/sexp_conv/custom_printf
# rewriters (CoAR's z351 switch lacks logs and fmt).
set -u
cd "$(dirname "$0")/.." || exit 2
ROOT=$(pwd)
SRC=$ROOT/benchmarks/sprouta/examples/sprout
PATCH=$ROOT/script/fetch/sprouta-generate-only.patch
EXPECTED=$ROOT/script/fetch/sprouta.expected
GEN=${SPROUTA_GEN:-$ROOT/sprouta-gen}
VERSION=${SPROUTA_VERSION:-opt}
NETS="p2pbox senderbox mailbox monobox bag"
ZIP_URL=https://zenodo.org/api/records/19600644/files/source.zip/content
ZIP_MD5=af84473df83d3d48a98c3888b413c9b4

if [ "${1:-}" = --build ]; then
  DIR=${2:?usage: $0 --build DIR}
  [ -e "$DIR" ] && { echo "refusing: $DIR exists" >&2; exit 2; }
  mkdir -p "$DIR" || exit 2
  curl -sSL --fail --retry 3 -o "$DIR/source.zip" "$ZIP_URL" || { echo "FAILED to download $ZIP_URL" >&2; exit 1; }
  got=$(md5sum < "$DIR/source.zip" | cut -d' ' -f1)
  [ "$got" = "$ZIP_MD5" ] || { echo "CHECKSUM MISMATCH: source.zip md5 $got, expected $ZIP_MD5" >&2; exit 1; }
  # The zip carries macOS metadata (__MACOSX/, .DS_Store) beside the 39 source files.
  ( cd "$DIR" && unzip -q source.zip -x '__MACOSX/*' '*.DS_Store' ) || exit 1
  echo "zenodo 10.5281/zenodo.19600644 source.zip md5 $ZIP_MD5" > "$DIR/SOURCE"
  ( cd "$DIR" && patch -p1 < "$PATCH" ) || exit 2
  ( cd "$DIR/query-generator" && opam exec --switch="${OPAM_SWITCH:-5.3.0}" -- dune build ./main.exe ) || exit 1
  echo "built $DIR/query-generator/_build/default/main.exe"
  exit 0
fi

OUT=${1:-benchmarks/sprouta-generated}
[ -x "$GEN" ] || { echo "no generator at $GEN (run $0 --build DIR and link it as sprouta-gen)" >&2; exit 2; }
[ -d "$SRC" ] || { echo "no protocols at $SRC (run script/fetch_benchmarks.sh sprouta)" >&2; exit 2; }
[ -e "$OUT" ] && { echo "refusing: $OUT exists" >&2; exit 2; }
mkdir -p "$OUT/gclts" || exit 2
OUT=$(cd "$OUT" && pwd)
"$GEN" --version > "$OUT/GENERATOR" 2>&1
printf 'instance\tprotocol\tnetwork\tkind\texpected\n' > "$OUT/instances.tsv"
printf 'protocol\trow\tparties\tnetwork\texpected\tgclts\timpl\tgenerator\n' > "$OUT/protocols.tsv"
grep -v '^#' "$EXPECTED" | while IFS=$'\t' read -r p row parties ep2p esb emb emonob ebag _src; do
  first=""
  for net in $NETS; do
    case $net in
    p2pbox) e=$ep2p ;; senderbox) e=$esb ;; mailbox) e=$emb ;; monobox) e=$emonob ;; bag) e=$ebag ;;
    esac
    D=$OUT/$net
    mkdir -p "$D" || exit 2
    cp "$SRC/$p" "$D/$p" || { echo "FAIL $p: no protocol file"; continue; }
    # The generator names its output directories after its argument relative to its working directory.
    line=$(cd "$D" && "$GEN" --generate-only "$p" "$net" "$VERSION" 2> "$D/$p.stderr" | grep '^SPROUT-GEN')
    [ -s "$D/$p.stderr" ] || rm -f "$D/$p.stderr"
    rm -f "$D/$p"
    [ -n "$line" ] || { echo "FAIL $p $net: generator printed no SPROUT-GEN line"; continue; }
    G=$D/$p-generated-gclts
    if [ -z "$first" ]; then
      mv "$G" "$OUT/gclts/" || exit 2
      first=$net
      ng=0
      for f in "$OUT/gclts/$p-generated-gclts"/*.hes; do
        [ -e "$f" ] || continue; ng=$((ng+1))
        printf '%s\t%s\t-\tgclts\tinvalid\n' "${f#$ROOT/}" "$p" >> "$OUT/instances.tsv"
      done
    else
      diff -r -q "$G" "$OUT/gclts/$p-generated-gclts" > /dev/null ||
        echo "FAIL $p $net: GCLTS instances differ from those generated for $first"
      rm -rf "$G"
    fi
    ni=0
    for f in "$D/$p-generated"/*.hes; do
      [ -e "$f" ] || continue; ni=$((ni+1))
      case $e in Y) x=invalid ;; N) x=some-valid ;; *) x=unknown ;; esac
      printf '%s\t%s\t%s\timpl\t%s\n' "${f#$ROOT/}" "$p" "$net" "$x" >> "$OUT/instances.tsv"
    done
    printf '%s\t%s\t%s\t%s\t%s\t%d\t%d\t%s\n' "$p" "$row" "$parties" "$net" "$e" "$ng" "$ni" "${line#SPROUT-GEN }" \
      >> "$OUT/protocols.tsv"
  done
done
n=$(($(wc -l < "$OUT/instances.tsv") - 1))
echo "generated $n instances ($(grep -c '	gclts	' "$OUT/instances.tsv") GCLTS) for $(($(wc -l < "$OUT/protocols.tsv") - 1)) protocol-network pairs into $OUT"
echo DONE
