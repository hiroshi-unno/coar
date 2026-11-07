#! /bin/bash
# Wrapper for invoking MuVal for (non-)termination verification in accordance with the method specified
# for termCOMP, on the rewritten C pipeline: the new Ptr2Arr (athena/Ptr2ArrFC, on Frama-C), clang 19.1.7,
# llvm2lts (athena/llvm2lts), then MuVal on the T2 file.  The arguments are those of solver.sh beside it
# (--name, --timeout=N, --category=CAT, then the input file); the answer is MuVal's YES or NO, MAYBE
# only for a reachable memory-safety violation under C_MemorySafety, and abort for every lack of an
# answer (a step that refused the input, MuVal's own MAYBE, a run that printed nothing, a category
# this pipeline does not take), so that the two are told apart.
#
# Categories:
#   C           Ptr2Arr, llvm2lts --mode int-bitwise --unbounded-nondet, -p ltsterm: integers read
#               as mathematical integers, as termCOMP's C semantics reads them (no over- or underflow,
#               and a __VERIFIER_nondet_T is any integer, not one of T's range), with the bit
#               operations by a constant in infinite two's complement
#   C_assume    the same with Ptr2Arr --assume-safety (an execution ends at its first out-of-bounds
#               access, so the verdict is about the in-bounds executions)
#   C_Mod       Ptr2Arr --wrap-integers, llvm2lts --mode int (nondet values in their type's range),
#               -p ltsterm: unsigned arithmetic and the
#               narrowing and sign-changing conversions wrap as in C (llvm2lts reads Ptr2Arr's
#               __p2a_wrap_k calls as the reduction into the type's range); signed arithmetic is
#               assumed not to overflow
#   C_BV        Ptr2Arr, llvm2lts --mode bv, -p ltstermbv (every value a bit-vector of its C width)
#   C_MemorySafety
#               termination of Ptr2Arr --assume-safety (-p ltsterm; an execution ends at its first
#               memory-safety violation, which is sound here: a program with a reachable violation has
#               no correct answer, and on a safe one no execution is ended) and, in parallel, safety of Ptr2Arr --memory-safety --violation-markers=reach-error
#               --memtrack-check=none (every invalid dereference or free calls reach_error, which
#               llvm2lts reads as the error location; -p ltssafe), both in C's integer reading.  A leak is not checked: it does not
#               make the program's meaning undefined, and most termination tasks never free.
#               A reachable violation gives MAYBE; otherwise (safe, no answer, or a safety side that
#               could not be translated) the termination answer.  A termination side that refuses
#               gives abort before the safety side runs.  A termination YES or NO waits for the
#               safety side until SAFETY_MARGIN_S (3) seconds before --timeout, and is the answer
#               when that side has not answered NO by then; a termination side without an answer
#               stops the safety side, and a safety NO stops the termination side.
#   Integer_Transition_Systems   its-conversion, then -p pltsterm, as solver.sh does
# Other categories answer abort.
#
# Every Ptr2Arr run of an Int route is given --unbounded-regions: llvm2lts reads an array as having no
# length, so the region arrays are unbounded, as the memory of termCOMP's C semantics is, and no
# allocation can exhaust one.  Not in C_BV: there the index is a bit-vector, which wraps past 2^31.  Without it a nondeterministic-length alloca or variable-length array reaches the exhaustion
# check, which with the reach-error markers is a violation, and the answer is a spurious MAYBE.
#
# Every Ptr2Arr run is given --scalar-cells: a region of one alloca cell that each call allocates once
# and no pointer moves from or out of is kept in a scalar, so that a bound read through such a pointer
# needs no invariant about an array.
#
# llvm2lts is given --hoist=yes: an array cell no transition of a loop writes (a bound read through a
# pointer, which Ptr2Arr keeps in a region array) is read once before the loop, so that proving
# termination needs no invariant about the array; llvm2kittel did the same with its own hoister.
#
# A step that refuses its input (Ptr2Arr outside its fragment, clang, llvm2lts's UNKNOWN for a
# construct it does not translate) gives abort, with the reason on stderr; on C_MemorySafety's safety
# side it only means that no violation is reported.
#
# Every C category is one run of CoAR under an Athena configuration this script writes (the reading of
# the integers, the options above, the MuVal configuration, clang, Frama-C's share directory): CoAR runs
# Ptr2Arr (linked in), clang, llvm2lts (linked in) and MuVal itself, -p cterm for a termination
# category and -p ctermmemsafe for C_MemorySafety, whose two sides are two runs of CoAR it starts and
# combines as described above; it answers UNSAFE for a reachable violation, written MAYBE here.
#
# The tools are found through these variables, whose defaults are where the image holding this pipeline
# puts them:
#   COAR_EXE (built with Frama-C 33 and llvm2lts), CONFIG_DIR (and WORKING_DIR, where CoAR runs: its
#   configs name nested ones by relative path), CLANG19, FRAMAC_SITE_SHARE (Frama-C's share directory).
# Intermediate files go to a fresh directory under $TMPDIR, removed at the end unless KEEP_WORK=1.

set -euo pipefail

WORKING_DIR="${WORKING_DIR:-/opt/coar}"
COAR_EXE="${COAR_EXE:-/usr/local/bin/coar}"
CONFIG_DIR="${CONFIG_DIR:-/opt/coar/config}"
CLANG19="${CLANG19:-/opt/coar/bin/llvm-19.1.7/bin/clang-19}"
FRAMAC_SITE_SHARE="${FRAMAC_SITE_SHARE:-/opt/coar/share/frama-c}"
# The same MuVal configuration as solver.sh, for every category.
TERM_CONFIG="$CONFIG_DIR/solver/muval_yesno.json"
# C_MemorySafety: how long before --timeout a termination answer stops waiting for the safety side.
SAFETY_MARGIN_S="${SAFETY_MARGIN_S:-3}"

category=""
timeout=""
args_to_coar=()
while (( $# > 0 )); do
    case $1 in
    --name )
        echo "MuVal"
        exit
        ;;
    --timeout=* )
        export timeout="${1#--timeout=}"
        shift
        ;;
    --category=* )
        category="${1#--category=}"
        shift
        ;;
    *)
        args_to_coar+=("$1")
        shift
        ;;
    esac
done

src=""
for a in "${args_to_coar[@]}"; do
  case "$a" in
    *.c|*.ari)
      src="$a"
      ;;
  esac
done

if [[ -z "$src" ]]; then
  echo "no .c or .ari input found" >&2
  exit 2
fi
src=$(realpath -- "$src")

work=$(mktemp -d "${TMPDIR:-/tmp}/termcomp_llvm2lts.XXXXXX")
cleanup() { [[ "${KEEP_WORK:-0}" == 1 ]] || rm -rf "$work"; }
trap cleanup EXIT

# The Athena configuration for INTEGERS (Unbounded, Modulo or Bit_vector) with the further fields
# EXTRA (JSON members, each followed by a comma), written to $work/athena.json.  The reading is
# written in full, so that a change of CoAR's defaults reaches no answer: the execution stops at
# undefined behaviour, and under Modulo and Bit_vector a signed overflow is undefined (Unbounded has
# no overflow and takes no such field).
athena_config() {
    local integers="$1" extra="${2:-}" keep="" overflow=""
    [[ "${KEEP_WORK:-0}" == 1 ]] && keep=", \"work_dir\": \"$work/steps\""
    [[ $integers == Unbounded ]] || overflow='"signed_overflow": ["Undefined"], '
    printf '["Athena", {"route": ["Llvm2lts"], "integers": ["%s"], %s"undefined_behaviour": ["Path_stops"], %s"regions": ["Unbounded_regions"], "hoist": ["Hoisted"], "solver": ["Filename", "%s"], "clang": "%s", "framac_share": "%s"%s}]\n' \
        "$integers" "$overflow" "$extra" "$TERM_CONFIG" "$CLANG19" "$FRAMAC_SITE_SHARE" "$keep" > "$work/athena.json"
}

# CoAR on the input under $work/athena.json as PROBLEM: its answer, the MAYBE of a lack of answer
# written abort, and the UNSAFE of a reachable violation written MAYBE, told apart on stderr.
solve_c() {
    cd "$WORKING_DIR"
    "$COAR_EXE" -c "$work/athena.json" -p "$1" --c-data-model LP64 "$src" | verdict
}

# MuVal's answer with its MAYBE (no answer: unknown or out of time) written abort, the MAYBE of
# this script being kept for a reachable violation.
verdict() {
    sed -u -e 's/^MAYBE$/abort/' -e 's/^UNSAFE$/MAYBE/'
}

case $category in
    Integer_Transition_Systems )
        base_name=$(basename -- "$src" .ari)
        its-conversion-static --to smt2 "$src" > "$work/$base_name.smt2"
        cd "$WORKING_DIR"
        "$COAR_EXE" -c "$TERM_CONFIG" -p "pltsterm" "$work/$base_name.smt2" | verdict
        ;;
    C )
        athena_config Unbounded
        solve_c cterm
        ;;
    C_assume )
        athena_config Unbounded '"memory": ["Assumed_safe"], '
        solve_c cterm
        ;;
    C_Mod )
        athena_config Modulo
        solve_c cterm
        ;;
    C_BV )
        athena_config Bit_vector
        solve_c cterm
        ;;
    C_MemorySafety )
        wait_s=""
        [[ "$timeout" =~ ^[0-9]+$ ]] && wait_s="\"safety_wait_s\": $(( timeout - SAFETY_MARGIN_S - SECONDS )), "
        athena_config Unbounded "\"memtrack\": [\"Not_checked\"], $wait_s"
        solve_c ctermmemsafe
        ;;
    * )
        echo "category ${category:-<none>} is not supported by the llvm2lts pipeline" >&2
        echo "abort"
        ;;
esac
