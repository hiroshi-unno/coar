#! /bin/bash
# Wrapper for invoking MuCyc/PCSat in accordance with the method specified for CHC-Comp 2026

set -euo pipefail

COAR_ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
COAR_MAIN_EXECUTABLE="${COAR_ROOT_DIR}/main.exe"

NEW_ARGS=()
for arg in "$@"; do
    if [ -e "$arg" ]; then
        NEW_ARGS+=("$(realpath "$arg")")
    else
        NEW_ARGS+=("$arg")
    fi
done

cd "${COAR_ROOT_DIR}"

export LD_LIBRARY_PATH="${COAR_ROOT_DIR}/lib/apron:${COAR_ROOT_DIR}/lib"

exec "${COAR_ROOT_DIR}/lib/ld-linux-x86-64.so.2" "${COAR_MAIN_EXECUTABLE}" "${NEW_ARGS[@]}"
