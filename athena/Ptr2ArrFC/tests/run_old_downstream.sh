#!/bin/bash
# Verification of this Ptr2Arr's outputs by the existing downstream: clang 3.6.2, opt, llvm2kittel
# and CoAR, as the termCOMP image (script/termcomp/Dockerfile) holds them.
#
# usage: tests/run_old_downstream.sh [--memory-safety|--assume-safety|--wrap-integers]
#                                    [--image IMG] [--timeout SEC] [--config CFG]
#                                    OUTDIR [input.c ...]
#   (default inputs: tests/cases/*.c)
#   mode           the transformation's mode, and the category of script/termcomp/solver.sh
#                  whose downstream it is run with:
#                    (none)           ptr2arr             C                     -p ltsterm
#                    --assume-safety  ptr2arr --assume-safety  C_assume         -p ltsterm
#                    --memory-safety  ptr2arr --memory-safety  C_MemorySafety_Only  -p ltssafe
#                    --wrap-integers  ptr2arr --wrap-integers  C_Mod            -p ltsterm
#                  (C_Mod's SemanticAugmentor is not run: --wrap-integers does its work)
#   --image IMG    the image holding the downstream (default termcomp:latest)
#   --timeout SEC  wall-clock bound of each CoAR run (default 60)
#   --config CFG   CoAR config, relative to the image's /opt/coar (default
#                  config/solver/muval_yesno.json; the image may predate
#                  the config solver.sh names now)
#
# Two things the old downstream expects of its input and this Ptr2Arr does not give it, both
# supplied here:
#   - llvm2kittel --allocated-memory-info names the region arrays, one per line (it initialises
#     an array it names to nondet() rather than to zero); they are the record's regions[].array.
#   - reach_error must be declared noreturn: without it clang puts no `unreachable` after the
#     call, and llvm2kittel writes a transition to the error location followed by the rest of the
#     block, a malformed T2 file. The declaration `void reach_error(void);` is given
#     __attribute__((__noreturn__)), and column `patched` says whether that happened.
#
# For each input, in OUTDIR/<name>/: the output <name>_Ptr2Arr.c, its record, the region list,
# the bitcode, <name>.t2 and the logs of each stage. One line per input goes to
# OUTDIR/summary.tsv:
#   name  transform  patched  clang  llvm2kittel  verdict
# where transform is ptr2arr's exit status (2 = refused as unsupported), clang and llvm2kittel are
# ok/fail/- (not reached), and verdict is CoAR's last line (YES/NO/MAYBE/...), TIMEOUT or ERROR
# (CoAR raised; see coar.err). The script ends with the counts of each verdict and the line DONE.
set -u
here=$(cd "$(dirname "$0")/.." && pwd)
exe="$here/_build/default/bin/ptr2arr.exe"
mode=normal; image=termcomp:latest; tlimit=60
config=config/solver/muval_yesno.json
while :; do
    case "${1:-}" in
        --memory-safety) mode=memory-safety; shift ;;
        --assume-safety) mode=assume-safety; shift ;;
        --wrap-integers) mode=wrap-integers; shift ;;
        --image) image=$2; shift 2 ;;
        --timeout) tlimit=$2; shift 2 ;;
        --config) config=$2; shift 2 ;;
        -*) echo "unknown option $1" >&2; exit 1 ;;
        *) break ;;
    esac
done
[ $# -ge 1 ] || { sed -n '4,9p' "$0" >&2; exit 1; }
out=$1; shift
[ -x "$exe" ] || { echo "no $exe: dune build --root $here" >&2; exit 1; }
docker image inspect "$image" > /dev/null 2>&1 || { echo "no image $image" >&2; exit 1; }
if [ $# -eq 0 ]; then set -- "$here"/tests/cases/*.c; fi
mkdir -p "$out" || exit 1
out=$(cd "$out" && pwd)

case $mode in
    normal) p2a_args=(); problem=ltsterm
        l2k_args=(--dump-ll --no-slicing --eager-inline) ;;
    assume-safety) p2a_args=(--assume-safety); problem=ltsterm
        l2k_args=(--dump-ll --no-slicing --eager-inline) ;;
    memory-safety) p2a_args=(--memory-safety); problem=ltssafe
        l2k_args=(--signedness-info --nondet-type-info=false --dump-ll --no-slicing --eager-inline) ;;
    wrap-integers) p2a_args=(--wrap-integers); problem=ltsterm
        l2k_args=(--signedness-info=false --nondet-type-info=true --dump-ll --no-slicing --eager-inline) ;;
esac

# Stage 1, on the host: the transformation, the region list and the reach_error declaration.
names=()
for src in "$@"; do
    name=$(basename "$src" .c)
    d="$out/$name"; rm -rf "$d"; mkdir -p "$d"
    "$exe" "${p2a_args[@]}" -o "$d/${name}_Ptr2Arr.c" --record="$d/$name.p2a.json" "$src" \
        > "$d/transform.log" 2>&1
    echo $? > "$d/transform.rc"
    [ -f "$d/${name}_Ptr2Arr.c" ] || continue
    python3 - "$d/$name.p2a.json" "$d/${name}_AllocatedMemory_Ptr2Arr.txt" <<'EOF' || continue
import json, sys
regions = json.load(open(sys.argv[1]))["regions"]
open(sys.argv[2], "w").write("".join(r["array"] + "\n" for r in regions))
EOF
    if grep -q '^\(extern \)\?void reach_error(void);' "$d/${name}_Ptr2Arr.c"; then
        sed -i 's/^\(\(extern \)\?void reach_error(void)\);/\1 __attribute__((__noreturn__));/' \
            "$d/${name}_Ptr2Arr.c"
        echo yes > "$d/patched"
    else
        echo no > "$d/patched"
    fi
    names+=("$name")
done

# Stage 2, in one container: clang, opt, llvm2kittel and CoAR on every transformed input.
cat > "$out/downstream.sh" <<EOF
#!/bin/bash
export PATH=/opt/llvm-3.6.2/bin:/usr/local/bin/dg/tools:\$PATH
for name in "\$@"; do
    d=/w/\$name; b=\$d/\$name
    echo - > \$d/clang; echo - > \$d/llvm2kittel
    clang -Wall -Wextra -c -emit-llvm -O0 \${b}_Ptr2Arr.c -o \${b}_Ptr2Arr.bc > \$d/clang.log 2>&1 \\
        || { echo fail > \$d/clang; continue; }
    echo ok > \$d/clang
    opt -mem2reg -tailcallelim \${b}_Ptr2Arr.bc -o \${b}_tailcallelim.bc >> \$d/clang.log 2>&1 \\
        || { echo fail > \$d/clang; continue; }
    (cd \$d && llvm2kittel ${l2k_args[*]} --allocated-memory-info=\${b}_AllocatedMemory_Ptr2Arr.txt \\
        --t2 \${b}_tailcallelim.bc > \$b.t2 2> \$d/llvm2kittel.log) \\
        || { echo fail > \$d/llvm2kittel; continue; }
    echo ok > \$d/llvm2kittel
    (cd /opt/coar && timeout $tlimit /usr/local/bin/coar -c $config -p $problem \$b.t2 \\
        > \$d/coar.out 2> \$d/coar.err)
    echo \$? > \$d/coar.rc
done
chown -R $(id -u):$(id -g) /w
EOF
if [ ${#names[@]} -gt 0 ]; then
    docker run --rm -v "$out":/w "$image" bash /w/downstream.sh "${names[@]}"
fi

# Stage 3: the summary.
printf 'name\ttransform\tpatched\tclang\tllvm2kittel\tverdict\n' > "$out/summary.tsv"
for src in "$@"; do
    name=$(basename "$src" .c); d="$out/$name"
    rd() { if [ -f "$d/$1" ]; then cat "$d/$1"; else echo -; fi; }
    verdict=-
    if [ -f "$d/coar.rc" ]; then
        rc=$(cat "$d/coar.rc"); last=$(tail -n 1 "$d/coar.out" | cut -d, -f1)
        if [ -n "$last" ]; then verdict=$last
        elif [ "$rc" = 124 ]; then verdict=TIMEOUT
        else verdict=ERROR; fi
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$(rd transform.rc)" "$(rd patched)" \
        "$(rd clang)" "$(rd llvm2kittel)" "$verdict" >> "$out/summary.tsv"
done
column -t -s $'\t' "$out/summary.tsv"
echo "inputs: $#"
tail -n +2 "$out/summary.tsv" | cut -f6 | sort | uniq -c
echo DONE
