#! /bin/bash
# Wrapper for invoking MuVal for (non-)termination verification in accordance with the method specified for termCOMP 2025

set -euo pipefail

WORKING_DIR="/opt/coar"
COAR_EXE="/usr/local/bin/coar"
CONFIG_DIR="/opt/coar/config"
LLVM_BIN_PATH="/opt/llvm-3.6.2/bin"
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

# echo "timeout=${timeout:-<none>}, category=${category:-<none>}"
# echo "args_to_coar=${args_to_coar:-<none>}"
case $category in
    Integer_Transition_Systems )
        base_name=$(basename -- "$src" .ari)

        reset_output_file "$base_name.smt2"
        its-conversion-static --to smt2 "$src" > "$base_name.smt2"

        $COAR_EXE -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "pltsterm" "$base_name.smt2"
        ;;
    C )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        $COAR_EXE -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltsterm" "${base_name}.t2"
        ;;
    C_Mod )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr_SemanticAugmentor.c"
        SemanticAugmentor "${base_name}_Ptr2Arr.c" "${base_name}_Metadata_Ptr2Arr.txt" --mode=only-nobv

        reset_output_file "${base_name}_Ptr2Arr_SemanticAugmentor.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr_SemanticAugmentor.c" -o "${base_name}_Ptr2Arr_SemanticAugmentor.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr_SemanticAugmentor.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --signedness-info=false --nondet-type-info=true --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        $COAR_EXE -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltsterm" "${base_name}.t2"
        ;;
    C_BV )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --signedness-info=true --nondet-type-info=false --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        reset_output_file "${base_name}_annotated.t2"
        TypeAnnotator "${base_name}_Ptr2Arr.c" "${base_name}_tailcallelim.ll" "${base_name}.t2" --mode=all

        $COAR_EXE -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltstermbv" "${base_name}_annotated.t2"
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

        setsid "$COAR_EXE" -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltsterm" "${base_name}.t2" > "$ltsterm_output" &
        ltsterm_pid=$!
        parallel_pids+=("$ltsterm_pid")
        setsid "$COAR_EXE" -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltssafe" "${base_name}_safety.t2" > "$ltssafe_output" &
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

        $COAR_EXE -c "$CONFIG_DIR/solver/muval_term_comp_parallel_exc_tbq_ar.json" -p "ltssafe" "${base_name}_safety.t2"
        ;;
    C_Print )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        cat "${base_name}.t2"
        ;;
    C_Print_Mod )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr_SemanticAugmentor.c"
        SemanticAugmentor "${base_name}_Ptr2Arr.c" "${base_name}_Metadata_Ptr2Arr.txt" --mode=only-nobv

        reset_output_file "${base_name}_Ptr2Arr_SemanticAugmentor.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr_SemanticAugmentor.c" -o "${base_name}_Ptr2Arr_SemanticAugmentor.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr_SemanticAugmentor.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --signedness-info=false --nondet-type-info=true --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        cat "${base_name}.t2"
        ;;
    C_Print_BV )
        export PATH="$LLVM_BIN_PATH:$DG_BIN_PATH:$PATH"

        base_name=$(basename -- "$src" .c)

        reset_output_file "${base_name}_PointsToSets.txt"
        reset_output_file "${base_name}_Metadata_Ptr2Arr.txt"
        reset_output_file "${base_name}_AllocatedMemory_Ptr2Arr.txt"
        reset_output_file "${base_name}_Ptr2Arr.c"
        Ptr2Arr "$src"

        reset_output_file "${base_name}_Ptr2Arr.bc"
        clang -Wall -Wextra -c -emit-llvm -O0 "${base_name}_Ptr2Arr.c" -o "${base_name}_Ptr2Arr.bc"

        reset_output_file "${base_name}_tailcallelim.bc"
        opt -mem2reg -tailcallelim "${base_name}_Ptr2Arr.bc" -o "${base_name}_tailcallelim.bc"

        reset_output_file "${base_name}.t2"
        reset_output_file "${base_name}_tailcallelim.ll"
        llvm2kittel --signedness-info=true --nondet-type-info=false --dump-ll --no-slicing --eager-inline --allocated-memory-info=${base_name}_AllocatedMemory_Ptr2Arr.txt --t2 "${base_name}_tailcallelim.bc" > "${base_name}.t2"

        reset_output_file "${base_name}_annotated.t2"
        TypeAnnotator "${base_name}_Ptr2Arr.c" "${base_name}_tailcallelim.ll" "${base_name}.t2" --mode=all

        cat "${base_name}_annotated.t2"
        ;;
    *)
        echo "no category specified. usage: solver --category=<category> <input file>"
        ;;
esac