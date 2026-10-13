#!/bin/bash

is_mac() {
        sw_vers > /dev/null 2>&1
        return $?
}

if is_mac; then
        date='gdate'
else
        date='date'
fi

if [ -z "$cmd" ]; then
        # echo "e.g., cmd=_build/default/main.exe ... $0"
        cmd="_build/default/main.exe"
fi

if [ "$1" != "--xargs" ]; then
        if [ -z "$timeout" ]; then
                echo "e.g., timeout=10 ... $0" >&2
                exit 2
        fi

        if [ -z "$options" ]; then
                echo "e.g., options='--synthesizer tb' ... $0" >&2
                exit 2
        fi

        if [ -z "$para" ]; then
                echo "e.g., para=3 ... $0" >&2
                exit 2
        fi

        if [ "$#" -eq 0 ]; then
                echo "provide benchmark paths or find arguments" >&2
                exit 2
        fi
        # GNU timeout accepts zero (no deadline), decimals and unit suffixes.
        # Retain that interface, but reject malformed durations before any workers.
        if [[ ! "$timeout" =~ ^[+]?([0-9]+([.][0-9]*)?|[.][0-9]+)([eE][+-]?[0-9]+)?[smhd]?$ ]] ||
                [[ ! "$para" =~ ^[0-9]+$ ]]; then
                echo "invalid timeout or parallelism setting" >&2
                exit 2
        fi

        # Materialize discovery before launching workers: failed find must not
        # produce a partial measurement. NUL records preserve literal filenames.
        RB_TMP=$(mktemp -d) || exit $?
        cleanup() {
                local status=$?
                trap - EXIT
                rm -rf -- "$RB_TMP"
                local cleanup_status=$?
                if [ "$status" -eq 0 ]; then
                        status=$cleanup_status
                fi
                exit "$status"
        }
        trap cleanup EXIT
        trap 'exit 130' INT
        trap 'exit 143' TERM
        find "$@" -type f -print0 >"$RB_TMP/list" || exit $?
        paths=()
        while IFS= read -r -d '' path; do
                paths+=("$path")
        done <"$RB_TMP/list" || exit $?
        if [ "${#paths[@]}" -eq 0 ]; then
                exit 0
        fi
        # Existing downstream CSV readers are unquoted comma/line readers.
        # Refuse unrepresentable keys rather than silently changing row identity.
        for path in "${paths[@]}"; do
                if [[ "$path" == *','* || "$path" == *'"'* || "$path" == *$'\n'* || "$path" == *$'\r'* ]]; then
                        printf 'benchmark path cannot be represented in result CSV: %q\n' "$path" >&2
                        exit 2
                fi
        done
        export RB_TOTAL=${#paths[@]}
        RB_START=$($date +%s) || exit $?
        export RB_START
        RB_DONE="$RB_TMP/done"
        : >"$RB_DONE" || exit $?
        export RB_DONE
        # Progress goes to stderr; workers append one completed-run marker each.
        for index in "${!paths[@]}"; do
                printf '%s\0%s\0' "$((index + 1))" "${paths[index]}" || exit $?
        done >"$RB_TMP/jobs" || exit $?
        xargs -0 -P "$para" -n 2 "$0" --xargs <"$RB_TMP/jobs"
        exit $?
fi

elapsed_total() {
        local s=$(( $($date +%s) - RB_START ))
        printf '%02d:%02d:%02d' $((s / 3600)) $((s % 3600 / 60)) $((s % 60))
}

index=$2
shift
echo "[$index/$RB_TOTAL] running $2 (elapsed $(elapsed_total))" 1>&2

progress() {
        echo >>"$RB_DONE"
        echo "[done $(wc -l <"$RB_DONE" | tr -d ' ')/$RB_TOTAL, elapsed $(elapsed_total)] $1" 1>&2
}

# dune build main.exe

run() {
        start_time=$($date +%s%N)
        output=$(timeout "$timeout" $cmd $options "$2")
        ret=$?

        if [ $ret = 124 ]; then
                progress "$2: timeout"
                printf '%s,timeout,\n' "$2"
                exit
        fi

        IFS="," read result iterations <<<"$output"

        end_time=$($date +%s%N)
        elapsed="0000000000$((end_time - start_time))"
        elapsed=$(sed -E 's/(.{9})$/.\1/' <<<"$elapsed" | sed -E 's/^0*([^0]*.)\./\1./')

        if [ "$ret" -eq 0 ] && [[ "$output" != *$'\n'* ]] && { [ "$result" = "valid" ] ||
                [ "$result" = "invalid" ] ||
                [ "$result" = "sat" ] ||
                [ "$result" = "unsat" ] ||
                [ "$result" = "unknown" ] ||
                [ "$result" = "infeasible" ] ||
                [ "$result" = "YES" ] ||
                [ "$result" = "NO" ] ||
                [ "$result" = "MAYBE" ]; }; then
                progress "$2: ${output%%$'\n'*} (${elapsed}s)"
                printf '%s,%s,%s,%s\n' "$2" "$result" "$elapsed" "$iterations"
        elif [ "$1" -gt 0 ]; then
                echo "$2 Abort, restart!" 1>&2
                run $(( $1 - 1 )) "$2"
        else
                progress "$2: abort (${elapsed}s)"
                printf '%s,abort,%s,%s\n' "$2" "$elapsed" "$iterations"
        fi
}

run 1 "$2"
