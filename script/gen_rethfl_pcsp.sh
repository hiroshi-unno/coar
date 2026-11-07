#!/bin/bash
# Generate the extended CHC systems (pCSP: CHC with disjunctive heads) that ReTHFL hands to PCSat for the
# nu-HFL(Z) non-termination benchmarks of its repository, without solving them.
#
#   script/gen_rethfl_pcsp.sh --build DIR    clone and build the pinned ReTHFL and ml2hfl in DIR (outside this
#                                            tree), each in an opam switch of its own under DIR/opam
#   script/gen_rethfl_pcsp.sh [OUT]          generate into OUT (default benchmarks/pCSP/rethfl-aplas2020,
#                                            which is ignored); script/fetch_benchmarks.sh rethfl-aplas2020
#                                            runs this and checks the result against its manifest
#
# SOURCE.  ReTHFL (github.com/hopv/rethfl) is the tool of Katsura, Iwayama, Kobayashi and Tsukada, "A New
# Refinement Type System for Automated nu-HFL(Z) Validity Checking", APLAS 2020.  It reduces a nu-HFL(Z) validity
# problem to constraints on refinement-type templates; when the constraint set, in disjunctive normal form, has
# more than one disjunct in a clause head (for both the primal and the dual system), it is not a CHC system and
# ReTHFL writes it as SMT-LIB2 HORN (`chc_solver.ml`, `save_chc_to_smt2`) and calls PCSat on it.  Those files are
# what this script keeps.  The repository carries no licence, so neither the tool nor its inputs are shipped here.
# ml2hfl (github.com/Hogeyama/ml2hfl, "Reduce safety property verification problems of OCaml into nu-only HFL
# validity checking problems", built on code of the MoCHi model checker) translates an OCaml program into a
# nu-HFL(Z) problem; with -non-termination the problem is the program's non-termination.  It needs OCaml 4.08,
# which the main opam repository no longer carries, so its switch also uses the opam archive repository.
#
# WHAT IS RUN.  The ten inputs of benchmark/inputs/higher_nonterminating/ (non-termination of higher-order
# programs, by Hogeyama, 2019), taken from the repository's history at INPUTS_COMMIT (they were removed from the
# repository later), each with ReTHFL's default options and with --no-inlining, the two settings of the
# repository's 2020 benchmark driver (scripts/bench/backend/infer.py).  PCSat is replaced by a stub that
# answers unknown, which ends ReTHFL's run after the first system it writes, so each run yields exactly one
# file: OUT/<input>.smt2 and OUT/<input>-no-inlining.smt2.  The stub's answer does not affect the file, which is
# written before the call.
#   The same programs written in OCaml (INPUTS_DIR/ml/*.ml) take the repository's ML route (its scripts/infer
# runs ml2hfl on the program and ReTHFL on the result): ml2hfl -non-termination, then ReTHFL as above, giving
# OUT/<input>-ml.smt2 and OUT/<input>-ml-no-inlining.smt2.  unfoldr_nonterm.ml is left out: ml2hfl at the pinned
# commit stops on it with an exception.
#
# REPRODUCIBILITY.  ReTHFL names the file /tmp-or-OUT/fptprove-<Random.int 2^28>.smt2 after Random.self_init,
# so this script renames it; the contents are deterministic for a given ReTHFL commit (two runs agreed byte for
# byte on 2026-11-01), which is why the manifest can pin each file's sha256.  Files ReTHFL wrote at another commit
# differ in the numbering of unknowns (X<n>) and variables (name followed by a counter), not only in the name.
#
# RETHFL and ML2HFL name the binaries (default: rethfl and ml2hfl on PATH; --build DIR prints how to set them).
set -u
cd "$(dirname "$0")/.." || exit 2
ROOT=$(pwd)
RETHFL_URL=https://github.com/hopv/rethfl.git
# HEAD of hopv/rethfl on 2026-11-01 (2025-08-08, "fix a typo introduced in the previous commit").
RETHFL_COMMIT=cca07d6cef8224f585157252f6b958f5ba3a8341
# The last commit holding benchmark/inputs/higher_nonterminating/ (the parent of 7522698cb4, which removed it).
INPUTS_COMMIT=6aca90544fc1db11fa39642074dec8e3c1fed948
INPUTS_DIR=benchmark/inputs/higher_nonterminating
INPUTS="alternate fib_CPS_nonterm fixpoint_nonterm foldr_nonterm indirectHO_e indirect_e inf_closure loopHO passing_cond unfoldr_nonterm"
ML_INPUTS="alternate fib_CPS_nonterm fixpoint_nonterm foldr_nonterm indirectHO_e indirect_e inf_closure loopHO passing_cond"
ML2HFL_URL=https://github.com/Hogeyama/ml2hfl.git
# HEAD of Hogeyama/ml2hfl on 2026-11-01 (2020-05-31, "Update main.yml").
ML2HFL_COMMIT=541cc1ee633885d529b70e59880bd90c71d17b80
# HEAD of ocaml/opam-repository-archive on 2026-11-01: it holds the OCaml 4.08.1 compiler package.
OPAM_ARCHIVE_COMMIT=f5b3f8867e235645eb04f5ddf94ac85bb34d9c23
# ppx_deriving_cmdliner is not on opam at the version ReTHFL needs; its master on 2026-11-01.
PPX_CMDLINER_COMMIT=1f086651fe7f8dd98e371b09c6fcc4dbc6db1c7c
TIMEOUT=${RETHFL_TIMEOUT:-120}

if [ "${1:-}" = --build ]; then
  DIR=${2:?usage: $0 --build DIR}
  [ -e "$DIR" ] && { echo "refusing: $DIR exists" >&2; exit 2; }
  mkdir -p "$DIR" && DIR=$(cd "$DIR" && pwd) || exit 2
  command -v opam >/dev/null || { echo "MISSING TOOL: opam" >&2; exit 1; }
  export OPAMROOT=$DIR/opam OPAMYES=1
  git clone -q "$RETHFL_URL" "$DIR/rethfl" && git -C "$DIR/rethfl" checkout -q "$RETHFL_COMMIT" || exit 1
  opam init --bare --disable-sandboxing -n https://opam.ocaml.org || exit 1
  # ReTHFL's lock file names OCaml 4.14.2; its cmdliner, logs and fmt are pinned to the lock file's versions
  # because cmdliner 2 removed Term.eval, which rethfl_options.ml calls.
  opam switch create rethfl 4.14.2 || exit 1
  eval "$(opam env --switch=rethfl)"
  opam pin add -n ppx_deriving_cmdliner.dev \
    "git+https://github.com/hammerlab/ppx_deriving_cmdliner.git#$PPX_CMDLINER_COMMIT" || exit 1
  opam install cmdliner.1.3.0 logs.0.7.0 fmt.0.9.0 || exit 1
  opam install --deps-only "$DIR/rethfl/rethfl.opam" || exit 1
  ( cd "$DIR/rethfl" && dune build ./bin/main.exe ) || exit 1
  # ml2hfl: OCaml 4.08.1 (the version its CI builds with) and the library versions of its time (core v0.13,
  # December 2019); its README's build is copying the parser wrapper of the compiler version, then dune.
  git clone -q "$ML2HFL_URL" "$DIR/ml2hfl" && git -C "$DIR/ml2hfl" checkout -q "$ML2HFL_COMMIT" || exit 1
  opam switch create ml2hfl --packages=ocaml-base-compiler.4.08.1 \
    --repos="default,archive=git+https://github.com/ocaml/opam-repository-archive.git#$OPAM_ARCHIVE_COMMIT" || exit 1
  eval "$(opam env --switch=ml2hfl)"
  opam install dune.2.5.1 core.v0.13.0 re2.v0.13.0 batteries.3.1.0 yojson.1.7.0 fmt.0.8.8 ppx_deriving.4.5 || exit 1
  ( cd "$DIR/ml2hfl" && cp parser_wrapper_4.08.ml parser_wrapper.ml && dune build ./ml2hfl.exe ) || exit 1
  echo "built: RETHFL=$DIR/rethfl/_build/default/bin/main.exe ML2HFL=$DIR/ml2hfl/_build/default/ml2hfl.exe $0"
  exit 0
fi

OUT=${1:-$ROOT/benchmarks/pCSP/rethfl-aplas2020}
RETHFL=${RETHFL:-rethfl}
ML2HFL=${ML2HFL:-ml2hfl}
command -v "$RETHFL" >/dev/null || { echo "no ReTHFL binary: set RETHFL (see $0 --build)" >&2; exit 1; }
command -v "$ML2HFL" >/dev/null || { echo "no ml2hfl binary: set ML2HFL (see $0 --build)" >&2; exit 1; }
if [ -d "$OUT" ] && [ -n "$(ls -A "$OUT" 2>/dev/null)" ]; then
  echo "refusing: $OUT is not empty" >&2; exit 2
fi
mkdir -p "$OUT" && OUT=$(cd "$OUT" && pwd) || exit 2
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT

# The inputs: only INPUTS_COMMIT's blobs under INPUTS_DIR are transferred.
if ! { git init -q "$tmp/r" && git -C "$tmp/r" remote add origin "$RETHFL_URL" &&
       git -C "$tmp/r" -c gc.auto=0 fetch -q --filter=blob:none --depth 1 origin "$INPUTS_COMMIT" &&
       git -C "$tmp/r" sparse-checkout set --no-cone "/$INPUTS_DIR/" &&
       git -C "$tmp/r" -c gc.auto=0 checkout -q FETCH_HEAD; }; then
  echo "FAILED to fetch $INPUTS_COMMIT of $RETHFL_URL" >&2; exit 1
fi

# ReTHFL calls PCSat as `$fptprove/script/rethfl.sh FILE` after chdir to $fptprove, and reads the second
# comma-separated field of its output as the answer.
mkdir -p "$tmp/stub/script"
printf '#!/bin/sh\necho stub,unknown\n' >"$tmp/stub/script/rethfl.sh"
chmod +x "$tmp/stub/script/rethfl.sh"
RETHFL_ABS=$(command -v "$RETHFL"); RETHFL_ABS=$(realpath "$RETHFL_ABS")
ML2HFL_ABS=$(command -v "$ML2HFL"); ML2HFL_ABS=$(realpath "$ML2HFL_ABS")

# One ReTHFL run on the nu-HFL(Z) file $1 with the options $3, keeping its one system as OUT/$2.smt2.
run_rethfl() {
  local src=$1 name=$2 opt=$3 d=$tmp/run/$2
  mkdir -p "$d"
  fptprove=$tmp/stub timeout "$TIMEOUT" "$RETHFL_ABS" $opt --smt-output-dir="$d" "$src" >"$d.log" 2>&1
  set -- "$d"/fptprove-*.smt2
  if [ $# -ne 1 ] || [ ! -f "$1" ]; then
    echo "   $name: expected one system, ReTHFL wrote $(ls "$d" | wc -l) files (log: $(tail -1 "$d.log"))" >&2
    fail=1; return
  fi
  cp "$1" "$OUT/$name.smt2" || fail=1
}

fail=0
for b in $INPUTS; do
  run_rethfl "$tmp/r/$INPUTS_DIR/$b.in" "$b" ""
  run_rethfl "$tmp/r/$INPUTS_DIR/$b.in" "$b-no-inlining" --no-inlining
done
mkdir -p "$tmp/hfl"
for b in $ML_INPUTS; do
  h=$tmp/hfl/$b.in
  if ! timeout "$TIMEOUT" "$ML2HFL_ABS" -non-termination "$tmp/r/$INPUTS_DIR/ml/$b.ml" >"$h" 2>"$h.err"; then
    echo "   $b-ml: ml2hfl failed ($(tail -1 "$h.err"))" >&2; fail=1; continue
  fi
  run_rethfl "$h" "$b-ml" ""
  run_rethfl "$h" "$b-ml-no-inlining" --no-inlining
done
echo "   $OUT: $(ls "$OUT" | wc -l) systems"
exit $fail
