#! /bin/bash
# Wrapper for invoking MuVal for (non-)termination verification in accordance with the method specified for termCOMP 2025

set -euo pipefail

WORKING_DIR="${WORKING_DIR:-/opt/coar}"
COAR_EXE="${COAR_EXE:-/usr/local/bin/coar}"
CONFIG_DIR="${CONFIG_DIR:-/opt/coar/config}"
# The MuVal configuration for every category: MuVal's termination entry.  Its PCSat chain keeps the
# qualifier enrichments (homogeneous qualifiers, argument transpositions) off and the plain
# synthesizer rather than the cell-guard one: on the C corpus those two later PCSat defaults turned
# answers into timeouts, and turning them back gained answers and time without a disagreement with
# the reference results.
TERM_CONFIG="$CONFIG_DIR/solver/muval_yesno.json"
LLVM_BIN_PATH="/opt/llvm-3.6.2/bin"
# The direct route of C, C_Mod and C_BV (and their C_Print* forms): the new Ptr2Arr on Frama-C,
# clang 19.1.7, then CoAR reading the LLVM IR itself.  Found through these variables, whose
# defaults are where an image holding this route is to put them.
PTR2ARR_FC="${PTR2ARR_FC:-/opt/coar/bin/ptr2arr_fc}"
FRAMAC_SITE_SHARE="${FRAMAC_SITE_SHARE:-/opt/coar/share/frama-c}"
CLANG19="${CLANG19:-/opt/coar/bin/llvm-19.1.7/bin/clang-19}"
DG_BIN_PATH="/usr/local/bin/dg/tools"

cd $WORKING_DIR

reset_output_file() {
    local output_file="$1"

    [ -e "$output_file" ] && chmod a+rw "$output_file"
    : > "$output_file"
}

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

# The direct route, run in $WORKING_DIR on $src: the new Ptr2Arr (for C_Mod with --wrap-integers,
# whose conversions are read modulo 2^N), clang 19.1.7 with the flags of the SV-COMP wrapper's
# direct route (script/svcomp/helpers/solver.sh, LP64), then CoAR with -p llvmterm (llvmtermbv
# for BV) and the direct frontend's configuration of the category, a file of config/llvmfront/:
# termCOMP's C reads integers as mathematical ones with nondeterministic values unbounded
# (unbounded.json), C_Mod reads them modulo 2^N (modulo.json), C_BV has every choice at its
# default (llvmfront.json).  Arguments: the reading (unbounded, modulo or bv), then the CoAR
# configuration (TERM_CONFIG to solve, printer.json to print the muCLP problem).  A step that
# refuses the input gives MAYBE, with its reason on stderr.
solve_direct() {
    local reading="$1" coar_config="$2"
    local base_name c_file problem=llvmterm
    local p2a_opts=(--data-model=LP64 --scalar-cells) llvm_config=()
    base_name=$(basename -- "$src" .c)
    case $reading in
        unbounded ) llvm_config=(--llvm-config "$CONFIG_DIR/llvmfront/unbounded.json") ;;
        modulo )
            p2a_opts+=(--wrap-integers)
            llvm_config=(--llvm-config "$CONFIG_DIR/llvmfront/modulo.json")
            ;;
        bv )
            problem=llvmtermbv
            llvm_config=(--llvm-config "$CONFIG_DIR/llvmfront/llvmfront.json")
            ;;
    esac

    c_file="${base_name}_Ptr2ArrFC.c"
    reset_output_file "$c_file"
    reset_output_file "${base_name}_Ptr2ArrFC.p2a.json"
    # the clang that compiles the output also preprocesses the input
    p2a_opts+=(--clang="$CLANG19")
    if ! env DUNE_DIR_LOCATIONS="frama-c:share:${FRAMAC_SITE_SHARE}" \
            "$PTR2ARR_FC" "${p2a_opts[@]}" -o "$c_file" --record="${base_name}_Ptr2ArrFC.p2a.json" "$src" >&2; then
        echo "MAYBE"
        return 0
    fi

    reset_output_file "${base_name}_direct.ll"
    if ! "$CLANG19" -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-finite-loops -ffp-contract=off \
            -fsanitize=shift-base -fsanitize-trap=shift-base \
            -Wno-error=int-conversion -Wno-error=implicit-function-declaration -Wno-error=implicit-int \
            -Wno-error=incompatible-function-pointer-types -g -m64 \
            "$c_file" -o "${base_name}_direct.ll"; then
        echo "MAYBE"
        return 0
    fi

    $COAR_EXE -c "$coar_config" -p "$problem" "${llvm_config[@]}" "${base_name}_direct.ll" || echo "MAYBE"
}

# echo "timeout=${timeout:-<none>}, category=${category:-<none>}"
# echo "args_to_coar=${args_to_coar:-<none>}"
case $category in
    Integer_Transition_Systems )
        base_name=$(basename -- "$src" .ari)

        reset_output_file "$base_name.smt2"
        its-conversion-static --to smt2 "$src" > "$base_name.smt2"

        $COAR_EXE -c "$TERM_CONFIG" -p "pltsterm" "$base_name.smt2"
        ;;
    C )
        solve_direct unbounded "$TERM_CONFIG"
        ;;
    C_assume )
        # The C pipeline under the assumption that the program is memory safe: Ptr2Arr ends every
        # execution at its first out-of-bounds access, so the verdict is about the in-bounds ones.
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr --assume-safety "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        $COAR_EXE -c "$TERM_CONFIG" -p "ltsterm" "${base_name}.t2"
        ;;
    C_Mod )
        solve_direct modulo "$TERM_CONFIG"
        ;;
    C_BV )
        solve_direct bv "$TERM_CONFIG"
        ;;
    C_MemorySafety )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src" #! This should be changed to Ptr2Arr --assume or somthing similar to ensure that the generated code is suitable for memory safety analysis.

        reset_output_file "${base_name}_safety_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_safety_Ptr2Arr.c"
        Ptr2Arr --memory-safety -o "${base_name}_safety_Ptr2Arr.c" "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        reset_output_file "${base_name}_safety_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_safety_Ptr2Arr.c" -o "${base_name}_safety_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        reset_output_file "${base_name}_safety_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_safety_Ptr2Arr.bc" -o "${base_name}_safety_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        reset_output_file "${base_name}_safety.t2"
        reset_output_file "${base_name}_safety_tailcallelim.ll"

        LLVM2KITTEL_OPTS="--signedness-info --nondet-type-info=false --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt"
        llvm2kittel $LLVM2KITTEL_OPTS --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"
        LLVM2KITTEL_OPTS="--signedness-info --nondet-type-info=false --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt"
        llvm2kittel $LLVM2KITTEL_OPTS --t2 "${base_name}_safety_tailcallelim.bc" > "${base_name}_safety.t2"


        ltsterm_output="${base_name}_ltsterm_$$.out"
        ltssafe_output="${base_name}_ltssafe_$$.out"
        reset_output_file "$ltsterm_output"
        reset_output_file "$ltssafe_output"

        parallel_pids=()
        kill_parallel_pid() {
            local pid="$1"
            if kill -0 -- "-$pid" 2>/dev/null; then
                kill -TERM -- "-$pid" 2>/dev/null || true
            elif kill -0 "$pid" 2>/dev/null; then
                kill -TERM "$pid" 2>/dev/null || true
            fi
        }
        cleanup_parallel_coar() {
            trap - INT TERM EXIT
            for pid in "${parallel_pids[@]:-}"; do
                kill_parallel_pid "$pid"
            done
            for pid in "${parallel_pids[@]:-}"; do
                wait "$pid" 2>/dev/null || true
            done
            rm -f "$ltsterm_output" "$ltssafe_output"
        }
        interrupt_parallel_coar() {
            cleanup_parallel_coar
            exit 130
        }
        trap cleanup_parallel_coar EXIT
        trap interrupt_parallel_coar INT TERM

        setsid "$COAR_EXE" -c "$TERM_CONFIG" -p "ltsterm" "${base_name}.t2" > "$ltsterm_output" &
        ltsterm_pid=$!
        parallel_pids+=("$ltsterm_pid")
        setsid "$COAR_EXE" -c "$TERM_CONFIG" -p "ltssafe" "${base_name}_safety.t2" > "$ltssafe_output" &
        ltssafe_pid=$!
        parallel_pids+=("$ltssafe_pid")

        wait "$ltsterm_pid" 2>/dev/null || true
        if wait "$ltssafe_pid"; then
            ltssafe_status=0
        else
            ltssafe_status=$?
        fi

        ltsterm_result=$(cat "$ltsterm_output" 2>/dev/null | tr -d '\r\n') || true
        ltssafe_result=$(tail -n 1 "$ltssafe_output" 2>/dev/null | cut -d',' -f1) || true

        : "${ltsterm_result:=TIMEOUT}"
        : "${ltssafe_result:=TIMEOUT}"

        if [[ "$ltsterm_result" == "YES" || "$ltsterm_result" == "NO" ]]; then
            if [[ "$ltssafe_result" == "NO" ]]; then
                result_output="MAYBE"
            else
                result_output="$ltsterm_result"
            fi
        else
            if [[ "$ltssafe_result" == "NO" ]]; then
                result_output="MAYBE"
            else
                result_output="$ltsterm_result"
            fi
        fi

        trap - INT TERM EXIT
        rm -f "$ltsterm_output" "$ltssafe_output"
        printf '%s\n' "$result_output"
        ;;
    C_MemorySafety_Only )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"

        reset_output_file "${base_name}_safety_Ptr2Arr.c"
        Ptr2Arr --memory-safety -o "${base_name}_safety_Ptr2Arr.c" "$src"

        reset_output_file "${base_name}_safety_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_safety_Ptr2Arr.c" -o "${base_name}_safety_Ptr2Arr.bc"

        reset_output_file "${base_name}_safety_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_safety_Ptr2Arr.bc" -o "${base_name}_safety_tailcallelim.bc"


        reset_output_file "${base_name}_safety.t2"
        reset_output_file "${base_name}_safety_tailcallelim.ll"

        LLVM2KITTEL_OPTS="--signedness-info --nondet-type-info=false --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt"
        llvm2kittel $LLVM2KITTEL_OPTS --t2 "${base_name}_safety_tailcallelim.bc" > "${base_name}_safety.t2"

        $COAR_EXE -c "$TERM_CONFIG" -p "ltssafe" "${base_name}_safety.t2"
        ;;
    C_Print )
        solve_direct unbounded "$CONFIG_DIR/solver/printer.json"
        ;;
    C_Print_Mod )
        solve_direct modulo "$CONFIG_DIR/solver/printer.json"
        ;;
    C_Print_BV )
        solve_direct bv "$CONFIG_DIR/solver/printer.json"
        ;;
    *)
        echo "no category specified. usage: solver --category=<category> <input file>"
        ;;
esac