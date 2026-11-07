#!/bin/bash
# A content-addressed cache of the LLVM IR that the Athena direct route makes from a C file (the C-to-C rewriting
# Ptr2ArrFC on Frama-C, then clang), so that a change to a later stage (the LLVM frontend, MuVal) can be compared
# over a corpus without running the rewriting and clang again for every file.
#
#   ll_cache.sh id   --clang VERSION --framac VERSION --commit COMMIT --stage p|w [--data-model LP64|ILP32]
#                    [--repo DIR] [--create]
#        prints the toolchain id: the first 16 hex digits of the sha256 of a descriptor naming everything that
#        decides the .ll -- clang's and Frama-C's version lines, the git tree ids of athena/Ptr2ArrFC and lib/Athena
#        at COMMIT (the rewriting and the step that chooses its options and clang's flags), the rewriting's stage
#        (p: plain, as for the Mathematical and Unbounded readings; w: --wrap-integers, as for Modulo), the data
#        model and the preprocessor.  With --create the descriptor is written to ROOT/ll/ID/TOOLCHAIN.
#   ll_cache.sh get  ID SOURCE.c [DEST]   exit 0 and the cached path on stdout (or a copy at DEST); exit 1 on a miss
#   ll_cache.sh put  ID SOURCE.c LL [--commit COMMIT] [--path NAME] [--move]
#        stores LL under the sha256 of SOURCE.c's bytes and appends a row to ROOT/ll/index.tsv
#        (source path, sha256, toolchain id, date, CoAR commit).  --move renames LL instead of copying it.
#   ll_cache.sh ls   [ID]                 the toolchain ids with their entry counts, or one id's descriptor and count
#
# ROOT is $COAR_CACHE, default ~/coar_cache.
#
# The key rule: an entry is (toolchain id, sha256 of the C bytes).  A change to anything the descriptor names gives a
# new id, so the old entries are simply not found; nothing is invalidated in place.  What the key does NOT see, and
# so must be ruled out by the checker below: a change to the rewriting that lives outside the two trees (a library it
# links), an environment variable, a clang or Frama-C rebuilt under an unchanged version line.
#
# The .ll's metadata carries the C file's name and the directory it was compiled in (source_filename, DIFile), so
# the same bytes under two names have .ll files that differ in those lines only; the key ignores the name on
# purpose.  A consumer that reads those names would need the name in the key.  The LLVM frontend under -p llvmterm
# and -p llvmsafe reads line numbers from the debug locations, not file names.
#
# Writes are atomic (a temporary file renamed into place) and the index is appended under flock, so parallel puts
# into one cache are safe.
set -u
ROOT=${COAR_CACHE:-$HOME/coar_cache}
die() { echo "ll_cache: $*" >&2; exit 2; }
sha_of() { sha256sum "$1" | cut -c1-64; }
act=${1:-}; shift || true
case "$act" in
  id)
    clang=; framac=; commit=; stage=; dm=LP64; repo=.; create=0
    while [ $# -gt 0 ]; do case $1 in
      --clang) clang=$2; shift 2;; --framac) framac=$2; shift 2;; --commit) commit=$2; shift 2;;
      --stage) stage=$2; shift 2;; --data-model) dm=$2; shift 2;; --repo) repo=$2; shift 2;;
      --create) create=1; shift;; *) die "id: unknown option $1";; esac; done
    [ -n "$clang" ] && [ -n "$framac" ] && [ -n "$commit" ] || die "id needs --clang, --framac and --commit"
    case $stage in p) st="ptr2arr plain";; w) st="ptr2arr --wrap-integers";; *) die "id: --stage p|w";; esac
    t1=$(git -C "$repo" rev-parse "$commit:athena/Ptr2ArrFC" 2>/dev/null) || die "no athena/Ptr2ArrFC at $commit"
    t2=$(git -C "$repo" rev-parse "$commit:lib/Athena" 2>/dev/null) || die "no lib/Athena at $commit"
    desc=$(printf 'clang=%s\nframac=%s\nptr2arrfc_tree=%s\nathena_tree=%s\nstage=%s\ndata_model=%s\npreprocessor=clang\nroute=direct\n' \
      "$clang" "$framac" "$t1" "$t2" "$st" "$dm")
    id=$(printf '%s\n' "$desc" | sha256sum | cut -c1-16)
    if [ $create = 1 ]; then mkdir -p "$ROOT/ll/$id"
      [ -e "$ROOT/ll/$id/TOOLCHAIN" ] || printf '%s\nfirst_commit=%s\n' "$desc" "$(git -C "$repo" rev-parse "$commit")" > "$ROOT/ll/$id/TOOLCHAIN"; fi
    echo "$id" ;;
  get)
    id=${1:?id}; src=${2:?source}; dest=${3:-}
    f="$ROOT/ll/$id/$(sha_of "$src").ll"
    [ -s "$f" ] || exit 1
    if [ -n "$dest" ]; then cp "$f" "$dest" || exit 2; else echo "$f"; fi ;;
  put)
    id=${1:?id}; src=${2:?source}; ll=${3:?ll}; shift 3; commit=-; name=$src; mv=0
    while [ $# -gt 0 ]; do case $1 in --commit) commit=$2; shift 2;; --path) name=$2; shift 2;; --move) mv=1; shift;;
      *) die "put: unknown option $1";; esac; done
    [ -e "$ROOT/ll/$id/TOOLCHAIN" ] || die "put: unknown toolchain id $id (create it with: id ... --create)"
    [ -s "$ll" ] || die "put: empty or missing $ll"
    s=$(sha_of "$src"); f="$ROOT/ll/$id/$s.ll"; tmp="$f.tmp.$$"
    if [ $mv = 1 ]; then mv "$ll" "$tmp" || exit 2; else cp "$ll" "$tmp" || exit 2; fi
    mv -f "$tmp" "$f" || exit 2
    { flock 9; printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$s" "$id" "$(date -u +%FT%TZ)" "$commit" >> "$ROOT/ll/index.tsv"; } 9>>"$ROOT/ll/.lock" ;;
  ls)
    if [ $# -ge 1 ]; then cat "$ROOT/ll/$1/TOOLCHAIN"; echo "entries=$(find "$ROOT/ll/$1" -name '*.ll' | wc -l)"
    else for d in "$ROOT"/ll/*/; do [ -e "$d/TOOLCHAIN" ] || continue
      printf '%s\t%s\t%s\n' "$(basename "$d")" "$(find "$d" -name '*.ll' | wc -l)" "$(grep -E '^(stage|clang)=' "$d/TOOLCHAIN" | tr '\n' ' ')"; done; fi ;;
  *) die "usage: ll_cache.sh id|get|put|ls ..." ;;
esac
