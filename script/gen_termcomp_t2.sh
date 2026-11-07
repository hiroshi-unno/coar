#!/bin/bash
# Translate the C programs of termCOMP's C category (the TPDB submodule benchmarks/term-comp, directory C/) into T2
# transition systems with CoAR's own Athena route, in a Docker image built from this repository.
#
#   script/gen_termcomp_t2.sh [OUT]   generate into OUT (default benchmarks/LTS/term-comp_llvm2lts, which is ignored);
#                                     script/fetch_benchmarks.sh termcomp-t2 runs this
#
# Needs Docker (the image is about 8 GB: run it on a machine where that may be built; where the root disk is small, a
# tmpfs as Docker's data root does), git, and the submodule benchmarks/term-comp checked out.  Run from the
# repository root of a full clone (the image is built from `git archive HEAD`).
#
# THE ROUTE, per program: main.exe -c <cfg> -p cterm <program>.c, cfg being
#   ["Athena", {"integers": ["Unbounded"], "regions": ["Unbounded_regions"], "hoist": ["Hoisted"],
#               "tail_recursion": ["Accumulated"], "control_flow": ["Simplified"], "work_dir": W}]
# which is the reading termCOMP's C category is run with (integers without a range and nondeterministic values
# unbounded, llvm2lts's --mode int-bitwise --unbounded-nondet; the rewriting's --unbounded-regions; llvm2lts's
# --hoist=yes; tail-call elimination also of `return n + f(x);` and `return n * f(x);`, exact with unbounded integers,
# llvm2lts's --tailcallelim-accumulator=yes; LLVM's simplifycfg before mem2reg, --simplifycfg=yes, which merges the
# empty block the rewriting's single return point leaves before a void function's return), on the llvm2lts route:
# the C-to-C rewriting Ptr2ArrFC on Frama-C, clang 19 to LLVM IR, llvm2lts to T2, LP64.  With work_dir set the intermediate files stay there, and the T2 file llvm2lts writes, <stem>.t2, is the output.
# The run is stopped as soon as that file is written (its size unchanged over half a second): what follows is MuVal
# solving it, which is not wanted here.  A run that ends without a T2 file is a refusal, whose reason is the
# `unknown:` (or `error:`) line it printed: a recursion other than a tail call (a T2 file is one transition system with
# no call stack), an operand llvm2lts cannot read, a call of a function without a body, a program outside the
# rewriting's fragment.  A run still without a T2 file after TIMEOUT seconds is stopped and recorded as a timeout.
#
# THE IMAGE is built from script/fetch/termcomp-t2.Dockerfile with a context holding `git archive HEAD` of the
# sources main.exe needs (CoAR.opam, dune, dune-project, main.ml, lib, config, athena/Ptr2ArrFC, athena/llvm2lts),
# tagged coar_termcomp_t2:<commit>.  The tools are not pinned (the base image, Ubuntu's clang-19 and llvm-19-dev and
# opam's packages are whatever they are on the day): what is required is that the set says what produced it, so the
# manifest records each version.  IMAGE=<name> uses an image already built instead.
#
# THE MANIFEST, OUT/MANIFEST.tsv: '#' lines give the date, the CoAR commit and the git tree id of each archived source
# directory, the image id, the base image's digest, the Frama-C, clang, LLVM, OCaml-binding, OCaml and OS versions,
# the configuration and command, the timeout, the submodule commit and the counts; then one line per program:
#   source_path  status  reason  sha256_source  sha256_output  output
# (status written, refused, timeout or failed; reason '-' unless refused; sha256_output and output '-' when no T2
# file was written).  Two runs in one image wrote the same files byte for byte: llvm2lts's output is a function of
# the program and the image, and holds no path or date.
#
# THE PIN, script/fetch/termcomp-t2.pinned (PINNED=...), tracked: one line per written T2 file,
#   source_path <TAB> sha256_output
# After generating, every program of this run whose output differs from the pin, is missing although pinned, or
# exists although not pinned is listed, and the script exits with status 3 (the files are still placed, and the
# manifest says which differ).  A pin is written from a run with PIN_WRITE=FILE; a new pin is a decision, taken
# when the image's tools or CoAR's translation change on purpose.  Programs outside this run (LIST=) are not compared.
#
# Settings: CFG_FIELDS (the configuration's fields other than work_dir, default the reading above), SUB (default benchmarks/term-comp), DIRS (directories of SUB to translate, default "C"), LIST (a file of
# source paths relative to SUB, to translate only those), JOBS (programs at a time, default 4), TIMEOUT (seconds per
# program, default 300), DOCKER_MEMORY (the container's memory limit, default 16g), KEEP_WORK=1 (keep the work
# directory, every run's files and logs included).
set -u
export LC_ALL=C   # one byte order for sort, join and the lists

OUT=${1:-benchmarks/LTS/term-comp_llvm2lts}
SUB=${SUB:-benchmarks/term-comp}
DIRS=${DIRS:-C}
LIST=${LIST:-}
IMAGE=${IMAGE:-}
DOCKER=${DOCKER:-docker}
DOCKERFILE=${DOCKERFILE:-script/fetch/termcomp-t2.Dockerfile}
JOBS=${JOBS:-4}
TIMEOUT=${TIMEOUT:-300}
DOCKER_MEMORY=${DOCKER_MEMORY:-16g}
PINNED=${PINNED:-script/fetch/termcomp-t2.pinned}
SRC_PATHS="CoAR.opam dune dune-project main.ml lib config athena/Ptr2ArrFC athena/llvm2lts"
CFG_FIELDS=${CFG_FIELDS:-'"integers": ["Unbounded"], "regions": ["Unbounded_regions"], "hoist": ["Hoisted"], "tail_recursion": ["Accumulated"], "control_flow": ["Simplified"]'}

die() { echo "gen_termcomp_t2: $*" >&2; exit 1; }
for t in sha256sum git; do command -v $t >/dev/null || die "$t is needed"; done
$DOCKER version >/dev/null 2>&1 || die "Docker is needed (DOCKER='$DOCKER' does not answer)"
[ -f "$DOCKERFILE" ] || die "no $DOCKERFILE (run from the repository root)"
[ -d "$SUB/C" ] || die "the submodule $SUB is not checked out"
[ -z "$LIST" ] || [ -f "$LIST" ] || die "no list $LIST"
if [ -d "$OUT" ] && [ -n "$(ls -A "$OUT" 2>/dev/null)" ]; then die "$OUT is not empty"; fi

W=$(mktemp -d "${TMPDIR:-/tmp}/termcomp_t2.XXXXXX") || exit 1
if [ -n "${KEEP_WORK:-}" ]; then echo "work directory: $W"; else trap 'rm -rf "$W"' EXIT; fi
mkdir -p "$W/in" "$W/out" || exit 1

commit=$(git rev-parse HEAD) || die "not in a git checkout"
trees=$(for p in $SRC_PATHS; do printf '%s=%s ' "$p" "$(git rev-parse "HEAD:$p" | cut -c1-12)"; done)
if [ -z "$IMAGE" ]; then
  [ -z "$(git status --porcelain --untracked-files=no -- $SRC_PATHS)" ] ||
    echo "note: the working tree differs from HEAD under $SRC_PATHS; the image is built from HEAD ($commit)"
  IMAGE="coar_termcomp_t2:$(git rev-parse --short=10 HEAD)"
  mkdir -p "$W/ctx/src" || exit 1
  git archive HEAD -- $SRC_PATHS | tar -x -C "$W/ctx/src" || die "cannot archive HEAD"
  cp "$W/ctx/src/CoAR.opam" "$W/ctx/CoAR.opam" && echo "$commit" > "$W/ctx/src/COAR_COMMIT" || exit 1
  echo "building $IMAGE (about 35 minutes without a cache; the log is $W/build.log while it runs)"
  DOCKER_BUILDKIT=1 $DOCKER build --build-arg OPAMJOBS="$JOBS" -t "$IMAGE" -f "$DOCKERFILE" "$W/ctx" > "$W/build.log" 2>&1 ||
    { tail -30 "$W/build.log" >&2; die "the image build failed"; }
fi
image_id=$($DOCKER image inspect -f '{{.Id}}' "$IMAGE") || die "no image $IMAGE"
# the base image's digest as the build resolved it (BuildKit's log names it), else as the local image records it
base_digest=$(grep -o 'ocaml/opam:ubuntu-24.04-ocaml-5.4@sha256:[0-9a-f]*' "$W/build.log" 2>/dev/null | head -1)
[ -n "$base_digest" ] || base_digest=$($DOCKER image inspect -f '{{join .RepoDigests " "}}' ocaml/opam:ubuntu-24.04-ocaml-5.4 2>/dev/null)

# the programs, as paths relative to SUB
if [ -n "$LIST" ]; then grep -v '^#' "$LIST" | sed '/^$/d'
else for d in $DIRS; do (cd "$SUB" && find "$d" -name '*.c' -type f); done; fi | LC_ALL=C sort -u > "$W/list"
[ -s "$W/list" ] || die "no programs"
while read -r p; do
  [ -f "$SUB/$p" ] || die "missing $SUB/$p"
  mkdir -p "$W/in/$(dirname "$p")" && cp "$SUB/$p" "$W/in/$p" || exit 1
done < "$W/list"
chmod -R a+rwX "$W"

cat > "$W/run.sh" <<'EOF'
# Runs in the image as user opam, from CoAR's root (the configurations name nested files by relative path).
cd /home/opam/coar || exit 1
one() {
  p=$1; o=/w/out/${p%.c}; mkdir -p "$o/work"
  printf '["Athena", {%s, "work_dir": "%s"}]\n' "$CFG_FIELDS" "$o/work" > "$o/athena.json"
  setsid ./_build/default/main.exe -c "$o/athena.json" -p cterm "/w/in/$p" > "$o/stdout" 2> "$o/stderr" &
  pid=$!; start=$(date +%s); st=
  while kill -0 "$pid" 2>/dev/null; do
    t=$(ls "$o"/work/*.t2 2>/dev/null | head -1)
    if [ -n "$t" ]; then
      s=$(stat -c %s "$t"); sleep 0.5
      if [ "$s" -gt 0 ] && [ "$(stat -c %s "$t")" = "$s" ]; then st=stopped; break; fi
    fi
    [ $(( $(date +%s) - start )) -ge "$TIMEOUT" ] && { st=timeout; break; }
    sleep 0.2
  done
  if [ -n "$st" ]; then kill -TERM -- "-$pid" 2>/dev/null; sleep 2; kill -KILL -- "-$pid" 2>/dev/null; fi
  wait "$pid"; rc=$?
  t=$(ls "$o"/work/*.t2 2>/dev/null | head -1)
  if [ -n "$t" ]; then cp "$t" "$o/out.t2"; status=written; reason=-
  elif [ "$st" = timeout ]; then status=timeout; reason="no T2 file after ${TIMEOUT} s"
  else
    reason=$(grep -m1 -E '^(unknown|error):' "$o/stderr" | sed 's/^unknown: //' | tr '\t' ' ')
    if [ -n "$reason" ]; then status=refused; else status=failed; reason="exit status $rc, no reason printed"; fi
  fi
  printf '%s\t%s\t%s\n' "$p" "$status" "$reason" >> /w/status.tsv
}
export -f one
: > /w/status.tsv
xargs -P "$JOBS" -I{} bash -c 'one "$1"' _ {} < /w/list
eval $(opam env)
{ printf 'coar_commit_in_image\t%s\n' "$(cat COAR_COMMIT 2>/dev/null)"
  printf 'frama_c\t%s\n' "$(frama-c -version 2>/dev/null | head -1)"
  printf 'clang\t%s\n' "$(clang-19 --version | head -1)"
  printf 'llvm\t%s\n' "$(llvm-config-19 --version)"
  printf 'ocaml_llvm_bindings\t%s\n' "$(opam list --installed -s --columns=name,version llvm 2>/dev/null | tr -s ' ' | tr '\n' ' ')"
  printf 'frama_c_opam\t%s\n' "$(opam list --installed -s --columns=version frama-c 2>/dev/null | tr '\n' ' ')"
  printf 'ocaml\t%s\n' "$(ocamlc -version)"
  printf 'os\t%s\n' "$(. /etc/os-release; echo "$PRETTY_NAME")"
} > /w/env.tsv
echo "translated $(wc -l < /w/status.tsv) programs"
EOF

echo "translating $(wc -l < "$W/list") programs in $IMAGE, $JOBS at a time, ${TIMEOUT}s each"
$DOCKER run --rm --memory="$DOCKER_MEMORY" --user opam -v "$W:/w" -e JOBS="$JOBS" -e TIMEOUT="$TIMEOUT" \
  -e CFG_FIELDS="$CFG_FIELDS" "$IMAGE" bash /w/run.sh || die "the container failed"
[ "$(wc -l < "$W/status.tsv")" -eq "$(wc -l < "$W/list")" ] ||
  die "the translation stopped early: $(wc -l < "$W/status.tsv") of $(wc -l < "$W/list")"
env_of() { awk -F'\t' -v k="$1" '$1 == k { print $2 }' "$W/env.tsv"; }

mkdir -p "$OUT" || exit 1
body="$W/manifest_body.tsv"; : > "$body"
while read -r p; do
  IFS=$'\t' read -r _ st reason < <(awk -F'\t' -v p="$p" '$1 == p' "$W/status.tsv")
  ss=$(sha256sum < "$SUB/$p" | cut -d' ' -f1); so=-; o=-
  f="$W/out/${p%.c}/out.t2"
  if [ "$st" = written ]; then
    so=$(sha256sum < "$f" | cut -d' ' -f1); o="${p%.c}.t2"
    mkdir -p "$OUT/$(dirname "$o")" && cp "$f" "$OUT/$o" || die "cannot place $o"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$p" "$st" "${reason:--}" "$ss" "$so" "$o" >> "$body"
done < "$W/list"

M="$OUT/MANIFEST.tsv"
{
  echo "# termCOMP's C programs as T2 transition systems, CoAR's Athena route (script/gen_termcomp_t2.sh)"
  echo "# date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# coar commit: $commit (image built from it: $(env_of coar_commit_in_image))"
  echo "# coar source trees: $trees"
  echo "# image: $IMAGE $image_id"
  echo "# base image: ocaml/opam:ubuntu-24.04-ocaml-5.4 ${base_digest:-digest unknown}"
  echo "# frama-c: $(env_of frama_c) (opam $(env_of frama_c_opam))"
  echo "# clang: $(env_of clang)"
  echo "# llvm: $(env_of llvm); OCaml bindings: $(env_of ocaml_llvm_bindings)"
  echo "# ocaml: $(env_of ocaml); os: $(env_of os); data model LP64"
  echo "# configuration: [\"Athena\", {$CFG_FIELDS, \"work_dir\": <dir>}]"
  echo "# command: main.exe -c <configuration> -p cterm <program>.c, stopped once llvm2lts has written <dir>/<stem>.t2; ${TIMEOUT}s"
  echo "# submodule: $SUB at $(git -C "$SUB" rev-parse HEAD 2>/dev/null || echo unknown) (https://github.com/TermCOMP/TPDB)"
  echo "# counts: $(cut -f2 "$body" | sort | uniq -c | awk '{printf "%s%s %s", (NR>1?", ":""), $2, $1}')"
  echo "# source_path	status	reason	sha256_source	sha256_output	output"
  cat "$body"
} > "$M"
echo "$OUT: $(grep -c $'\twritten\t' "$M") T2 files placed; $(grep '^# counts' "$M" | cut -c3-)"

if [ -n "${PIN_WRITE:-}" ]; then
  { echo "# T2 outputs of script/gen_termcomp_t2.sh, pinned: source_path<TAB>sha256 of the output"
    echo "# from the run of $(sed -n 's/^# date: //p' "$M"), CoAR $commit, image $image_id"
    echo "# $(sed -n 's/^# \(frama-c: .*\)/\1/p' "$M"); $(sed -n 's/^# \(clang: .*\)/\1/p' "$M"); $(sed -n 's/^# \(llvm: .*\)/\1/p' "$M")"
    awk -F'\t' '$5 != "-" { print $1 "\t" $5 }' "$body"; } > "$PIN_WRITE"
  echo "wrote the pin $PIN_WRITE ($(grep -vc '^#' "$PIN_WRITE") outputs)"
fi
if [ -f "$PINNED" ]; then
  diffs=$(join -t $'\t' -a1 -a2 -e - -o 0,1.2,2.2 \
            <(grep -v '^#' "$PINNED" | LC_ALL=C sort | join -t $'\t' - "$W/list") \
            <(awk -F'\t' '$5 != "-" { print $1 "\t" $5 }' "$body" | LC_ALL=C sort) | awk -F'\t' '$2 != $3')
  if [ -n "$diffs" ]; then
    echo "DIFFERS FROM THE PIN $PINNED ($(printf '%s\n' "$diffs" | wc -l) files; pinned, this run):"
    printf '%s\n' "$diffs" | awk -F'\t' '{ print "  " $1 "  " $2 "  " $3 }'
    exit 3
  fi
  echo "every output matches the pin $PINNED ($(grep -v '^#' "$PINNED" | LC_ALL=C sort | join -t $'\t' - "$W/list" | wc -l) files of this run)"
else
  echo "no pin at $PINNED: outputs not compared"
fi
