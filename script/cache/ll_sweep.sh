#!/bin/bash
# Compare two main.exe binaries on a C corpus from the LLVM frontend onwards, taking each file's .ll from the cache
# of ll_cache.sh and producing only the missing ones.
#
#   ll_sweep.sh --files LIST --corpus DIR --old BIN --new BIN --id-p ID [--id-w ID]
#               [--readings math,unb,mod] [--mode print|solve] [--act PRESET|ERE] [--producer BIN]
#               [--producer-commit COMMIT] [--verify N] [--out DIR] [-j N] [--timeout S]
#
#   LIST       C files, one per line, relative to DIR (the source path recorded in the cache index)
#   --id-p/-w  toolchain ids (ll_cache.sh id) of the plain rewriting (math, unb) and of --wrap-integers (mod)
#   --readings math: the default LLVM frontend configuration; unb: config/llvmfront/unbounded.json;
#              mod: config/llvmfront/modulo.json
#   --mode     print: -p llvmterm under config/solver/printer.json (the muCLP each binary writes; compared as text);
#              solve: -p llvmterm under the MuVal configuration the Athena direct route uses (verdicts compared)
#   --act      keep only the files whose .ll matches: a preset (nsw-arith: add/sub/mul/shl carrying nsw or nuw, and
#              sdiv/srem; div: sdiv/srem/udiv/urem) or an extended regular expression.  A file without a match is
#              listed as not acted on and not run.  The filter is only as good as the claim that the change acts
#              solely on those instructions; check it once against a full sweep's differing files.
#   --producer a main.exe with the rewriting and clang linked (an Athena build); a missing .ll is made by running it
#              under the Athena direct route with a work directory, stopped once the .ll exists, then put in the cache.
#              --producer-commit names its CoAR commit for the index.  Without it a miss is reported and the file skipped.
#   --verify N re-make N cached entries (a deterministic sample) with --producer and compare them with the cache
#              after removing the lines that carry the file's name and directory; a difference means the toolchain
#              id misses something that decides the .ll (a stale key): stop and widen the descriptor.
#
# Run from the repository root (configurations are named by relative path).  ROOT is $COAR_CACHE (~/coar_cache).
# Output under --out (default ./ll_sweep_out): files.tsv (file, stage, cache state), act.txt, per-run .out/.err/.rc
# under run/<reading>/<old|new>/, diff.txt (file reading) and summary.txt, which ends with DONE.
set -u
here=$(cd "$(dirname "$0")" && pwd); C="$here/ll_cache.sh"
files=; corpus=; old=; new=; idp=; idw=; readings=math; mode=print; act=; prod=; pc=-; verify=0; out=./ll_sweep_out; J=4; T=60
while [ $# -gt 0 ]; do case $1 in
  --files) files=$2;; --corpus) corpus=$2;; --old) old=$2;; --new) new=$2;; --id-p) idp=$2;; --id-w) idw=$2;;
  --readings) readings=$2;; --mode) mode=$2;; --act) act=$2;; --producer) prod=$2;; --producer-commit) pc=$2;; --verify) verify=$2;;
  --out) out=$2;; -j) J=$2;; --timeout) T=$2;; *) echo "ll_sweep: unknown option $1" >&2; exit 2;; esac; shift 2; done
[ -n "$files" ] && [ -n "$corpus" ] && [ -n "$old" ] && [ -n "$new" ] && [ -n "$idp" ] || { echo "ll_sweep: missing argument" >&2; exit 2; }
case $act in nsw-arith) act='= (add|sub|mul|shl) (nuw |nsw )|= (sdiv|srem) ';; div) act='= (sdiv|srem|udiv|urem) ';; esac
mkdir -p "$out"; out=$(cd "$out" && pwd); t0=$(date +%s)
export C corpus prod pc out T mode old new idp idw
stage_of() { case $1 in mod) echo w;; *) echo p;; esac; }
id_of() { [ "$1" = w ] && echo "$idw" || echo "$idp"; }
export -f stage_of id_of
stages=$(for r in ${readings//,/ }; do stage_of $r; done | sort -u)
[ -n "$idw" ] || ! grep -qx w <<<"$stages" || { echo "ll_sweep: the mod reading needs --id-w" >&2; exit 2; }

# Make one .ll: the Athena direct route with a work directory, stopped as soon as the .ll is written (the route then
# translates and solves, which the cache does not need; an Athena configuration's solver is a MuVal configuration
# only, so the printer cannot be named instead).  The file counts as written once its size has not changed for a
# second; a truncated one would show as a difference under --verify.
make_ll() { exe=$1; i=$2; wd=$3; src=$4
  echo "[\"Athena\", {\"route\": [\"Direct\"], \"integers\": [\"$i\"], \"work_dir\": \"$wd\"}]" > "$wd.json"
  timeout -s KILL 300 "$exe" -c "$wd.json" -p cterm "$src" > "$wd.out" 2> "$wd.err" < /dev/null & pid=$!
  for _ in $(seq 1 1500); do f=$(ls "$wd"/*_direct.ll 2>/dev/null | head -1)
    if [ -n "$f" ]; then a=$(stat -c %s "$f"); sleep 1; [ "$a" = "$(stat -c %s "$f")" ] && break; continue; fi; kill -0 $pid 2>/dev/null || break; sleep 0.2; done
  kill -KILL $pid 2>/dev/null; wait $pid 2>/dev/null; }
export -f make_ll

# 1. The .ll files: from the cache, or made and put.
mk() { rel=$1; st=$2; id=$(id_of $st); src="$corpus/$rel"
  if "$C" get "$id" "$src" >/dev/null; then echo -e "$rel\t$st\thit"; return; fi
  [ -n "$prod" ] || { echo -e "$rel\t$st\tmiss"; return; }
  b=$(basename "${rel%.c}"); wd=$(mktemp -d "$out/wd.XXXXXX")
  case $st in p) i=Mathematical;; w) i=Modulo;; esac
  make_ll "$prod" "$i" "$wd" "$src"; ll=$(ls "$wd"/*_direct.ll 2>/dev/null | head -1)
  if [ -n "$ll" ] && "$C" put "$id" "$src" "$ll" --path "$rel" --commit "$pc" --move; then echo -e "$rel\t$st\tmade"
  else echo -e "$rel\t$st\tfailed"; fi
  rm -rf "$wd" "$wd.json" "$wd.out" "$wd.err"; }
export -f mk
for st in $stages; do sed "s/\$/ $st/" "$files"; done | xargs -P "$J" -L 1 bash -c 'mk "$0" "$1"' | sort > "$out/files.tsv"
t1=$(date +%s)

# 1a. Stale-key check: re-make a sample and compare, the name-bearing lines removed.
if [ "$verify" -gt 0 ] && [ -n "$prod" ]; then : > "$out/verify.txt"
  norm() { grep -vE '^source_filename|DIFile\(|^; ModuleID' "$1"; }
  awk -F'\t' '$3=="hit"' "$out/files.tsv" > "$out/hits.tsv"
  awk -v n="$(wc -l < "$out/hits.tsv")" -v k="$verify" 'BEGIN{s=int(n/k); if(s<1)s=1} (NR-1)%s==0' "$out/hits.tsv" | head -n "$verify" | while IFS=$'\t' read rel st _; do
    id=$(id_of $st); cached=$("$C" get "$id" "$corpus/$rel"); wd=$(mktemp -d "$out/vd.XXXXXX")
    case $st in p) i=Mathematical;; w) i=Modulo;; esac
    make_ll "$prod" "$i" "$wd" "$corpus/$rel"; ll=$(ls "$wd"/*_direct.ll 2>/dev/null | head -1)
    if [ -z "$ll" ]; then r=nomake; elif cmp -s <(norm "$cached") <(norm "$ll"); then r=same; else r=STALE; fi
    echo -e "$rel\t$st\t$r" >> "$out/verify.txt"; rm -rf "$wd" "$wd.json" "$wd.out" "$wd.err"; done
  if grep -q STALE "$out/verify.txt"; then echo "ll_sweep: STALE cache entries (verify.txt): the toolchain id misses a factor" >&2; exit 3; fi
fi

# 2. The act filter.
: > "$out/act.txt"; : > "$out/not_acted.txt"
while read rel; do keep=1
  if [ -n "$act" ]; then keep=0
    for st in $stages; do f=$("$C" get "$(id_of $st)" "$corpus/$rel") || continue; grep -qE "$act" "$f" && keep=1; done; fi
  [ $keep = 1 ] && echo "$rel" >> "$out/act.txt" || echo "$rel" >> "$out/not_acted.txt"
done < "$files"
t2=$(date +%s)

# 3. Both binaries under each reading.
run() { rel=$1; r=$2; bin=$3; exe=$old; [ "$bin" = new ] && exe=$new
  st=$(stage_of $r); ll=$("$C" get "$(id_of $st)" "$corpus/$rel") || return 0
  case $r in math) x=();; unb) x=(--llvm-config config/llvmfront/unbounded.json);; mod) x=(--llvm-config config/llvmfront/modulo.json);; esac
  case $mode in print) cfg=./config/solver/printer.json;; solve) cfg=./config/solver/muval_yesno.json;; esac
  d="$out/run/$r/$bin/$(dirname "$rel")"; mkdir -p "$d"; b="$d/$(basename "${rel%.c}")"
  timeout -s TERM -k 5 "$T" "$exe" -c $cfg -p llvmterm "${x[@]}" "$ll" > "$b.out" 2> "$b.err" < /dev/null; echo $? > "$b.rc"; }
export -f run
for r in ${readings//,/ }; do for bin in old new; do sed "s/\$/ $r $bin/" "$out/act.txt"; done; done |
  xargs -P "$J" -L 1 bash -c 'run "$0" "$1" "$2"'
t3=$(date +%s)

# 4. Differences: printed text (or the verdict line) and status.
: > "$out/diff.txt"
for r in ${readings//,/ }; do while read rel; do b="${rel%.c}"; o="$out/run/$r/old/$b"; n="$out/run/$r/new/$b"
  [ -e "$o.rc" ] || continue
  if [ $mode = solve ]; then a=$(tail -1 "$o.out"); c=$(tail -1 "$n.out"); [ "$a" = "$c" ] && cmp -s "$o.rc" "$n.rc" && continue
  else cmp -s "$o.out" "$n.out" && cmp -s "$o.rc" "$n.rc" && continue; fi
  echo "$rel $r" >> "$out/diff.txt"; done < "$out/act.txt"; done
{ echo "files=$(wc -l < "$files") act_kept=$(wc -l < "$out/act.txt") not_acted=$(wc -l < "$out/not_acted.txt")"
  echo "ll: $(cut -f3 "$out/files.tsv" | sort | uniq -c | tr '\n' ' ')"
  echo "diff=$(wc -l < "$out/diff.txt") readings=$readings mode=$mode"
  echo "wall_s: ll=$((t1-t0)) act=$((t2-t1)) runs=$((t3-t2)) total=$(( $(date +%s) - t0 ))"
  echo DONE; } > "$out/summary.txt"
cat "$out/summary.txt"
