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

# Environment: timeout, para, options (required); cmd (the solver, default the tool);
# retries (restarts after an abort, default 1); reader=optpcsat (read the last line of
# OptPCSat's answer instead of the first line); logdir=DIR (keep each run's stdout and
# stderr as DIR/NAME.log and DIR/NAME.err); convert=smt2:P (print each input as SMT-LIB with
# the tool's printer under `-p P` first, and run the solver on that).  A foreign solver is
# `cmd=SOLVER options=FLAGS`.
# Rows on stdout are `path,verdict,seconds,iterations`; besides an answer the verdict is
# `timeout` (the limit, or the solver's own), `refused` (status 1 with a last stderr line
# `error: <reason>`, the reason in the fourth field) or `abort` (anything else that is not
# an answer: a crash, a signal, untrusted output).  reader=optpcsat keeps its own
# `Sat(Abort)` row for both of the last two.
# kill_after=SECONDS (default 30, 0 for none): a run still alive that long after the limit's TERM gets
# KILL (`timeout -k`).  A run that stops on TERM only through the OCaml runtime can be held
# far past its limit when its host runs out of memory (one ran 1,344 s past a 300 s limit
# until the kernel's OOM killer ended it, and stalled the run beside it); KILL frees the slot.
# Such a run still gets the limit's `timeout` row, since its deadline had passed.
# events=FILE (default LOGDIR/events.tsv with logdir, none without): one line per run that
# did not end by itself, `path<TAB>event<TAB>status<TAB>seconds`, the event being `restart`
# (an abort or refusal retried; the row shows only the last attempt) or `killed` (KILL after
# the grace).  The rows' format is unchanged; this file is where retries become visible.
if [ -z "$cmd" ]; then
        # echo "e.g., cmd=_build/default/main.exe ... $0"
        cmd="_build/default/main.exe"
fi
retries=${retries-1}
kill_after=${kill_after-30}
events=${events-}
reader=${reader-}
convert=${convert-}
logdir=${logdir-}

# limit_seconds DURATION
# Precondition: DURATION matches GNU timeout's syntax as checked below
# (an optional '+', a decimal with optional exponent, an optional unit s/m/h/d).
# Prints the duration in seconds exactly, as a plain decimal with no exponent,
# no leading '+', no superfluous zeros (e.g. 60, 1.5, 120, 10, 0.02); prints
# nothing for a zero duration, which GNU timeout reads as no deadline.  Fails
# when the exponent exceeds 300 in magnitude, which bounds the printed length.
# Only string arithmetic is used, so no precision is lost.
limit_seconds() {
        local value=${1#+} unit=1 mantissa exponent=0 sign=1 int frac digits
        local product='' carry=0 i d scale padding
        case $value in
        *s) value=${value%s} ;;
        *m) value=${value%m}; unit=60 ;;
        *h) value=${value%h}; unit=3600 ;;
        *d) value=${value%d}; unit=86400 ;;
        esac
        mantissa=${value%%[eE]*}
        int=${mantissa%%.*}
        frac=
        [[ $mantissa == *.* ]] && frac=${mantissa#*.}
        digits=$int$frac
        while [[ $digits == 0* ]]; do digits=${digits#0}; done
        [ -n "$digits" ] || return 0
        if [[ $value == *[eE]* ]]; then
                exponent=${value#*[eE]}
                [[ $exponent == -* ]] && sign=-1
                exponent=${exponent#[+-]}
                while [[ $exponent == 0?* ]]; do exponent=${exponent#0}; done
                [ "${#exponent}" -le 3 ] || return 1
                exponent=$((sign * 10#$exponent))
                [ "$exponent" -le 300 ] && [ "$exponent" -ge -300 ] || return 1
        fi
        for ((i = ${#digits} - 1; i >= 0; i--)); do
                d=$((${digits:i:1} * unit + carry))
                product=$((d % 10))$product
                carry=$((d / 10))
        done
        [ "$carry" -eq 0 ] || product=$carry$product
        # The value is product * 10^-scale.
        scale=$((${#frac} - exponent))
        if [ "$scale" -le 0 ]; then
                printf -v padding '%*s' "$((-scale))" ''
                printf '%s\n' "$product${padding// /0}"
                return 0
        fi
        if [ "${#product}" -le "$scale" ]; then
                printf -v padding '%*s' "$((scale - ${#product} + 1))" ''
                product=${padding// /0}$product
        fi
        int=${product:0:${#product}-scale}
        frac=${product:${#product}-scale}
        while [[ $frac == *0 ]]; do frac=${frac%0}; done
        if [ -n "$frac" ]; then
                printf '%s.%s\n' "$int" "$frac"
        else
                printf '%s\n' "$int"
        fi
}

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
        if [[ ! "$kill_after" =~ ^[0-9]+$ ]]; then
                echo "invalid kill_after setting (whole seconds)" >&2
                exit 2
        fi
        if [ -z "$events" ] && [ -n "$logdir" ]; then
                events="$logdir/events.tsv"
        fi
        export kill_after events
        if [[ ! "$retries" =~ ^[0-9]+$ ]] || { [ -n "$reader" ] && [ "$reader" != optpcsat ]; } ||
                [[ -n "$convert" && ! "$convert" =~ ^smt2:[A-Za-z0-9_]+$ ]]; then
                echo "invalid retries, reader or convert setting" >&2
                exit 2
        fi
        if [ -n "$logdir" ]; then
                mkdir -p -- "$logdir" || exit $?
        fi
        export retries reader convert logdir
        # GNU timeout accepts zero (no deadline), decimals and unit suffixes.
        # Retain that interface, but reject malformed durations before any workers.
        if [[ ! "$timeout" =~ ^[+]?([0-9]+([.][0-9]*)?|[.][0-9]+)([eE][+-]?[0-9]+)?[smhd]?$ ]] ||
                [[ ! "$para" =~ ^[0-9]+$ ]]; then
                echo "invalid timeout or parallelism setting" >&2
                exit 2
        fi
        # A timeout row records the limit in seconds as its elapsed time, so the
        # exact value is computed once here; empty means no deadline.
        RB_LIMIT=$(limit_seconds "$timeout") || {
                echo "timeout exponent out of range (at most 300 in magnitude)" >&2
                exit 2
        }
        export RB_LIMIT

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
        # A signal stops the workers, each of which stops its run's process group; the
        # workers are found as the children of this runner's xargs, never by name.
        RB_XARGS=
        stop_workers() {
                trap '' INT TERM
                if [ -n "$RB_XARGS" ]; then
                        kill -TERM $(ps -o pid= --ppid "$RB_XARGS") 2>/dev/null
                        kill -TERM "$RB_XARGS" 2>/dev/null
                        wait "$RB_XARGS" 2>/dev/null
                fi
                exit "$1"
        }
        trap 'stop_workers 130' INT
        trap 'stop_workers 143' TERM
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
        # Event records append between retries and can change a later solver input.
        # Protect that destination even when retained stdout/stderr logs are off.
        if [ -n "$events" ] && [ -e "$events" ]; then
                for path in "${paths[@]}"; do
                        if [ "$events" -ef "$path" ]; then
                                printf 'event destination aliases benchmark input: %s (%s)\n' "$events" "$path" >&2
                                exit 2
                        fi
                done
        fi
        if [ -n "$logdir" ]; then
                log_names=()
                for path in "${paths[@]}"; do
                        log_names+=("$(basename -- "$path")")
                done
                duplicate_log_names=$(set -o pipefail; printf '%s\n' "${log_names[@]}" | LC_ALL=C sort | uniq -d) || exit $?
                if [ -n "$duplicate_log_names" ]; then
                        printf 'duplicate log basename: %s\n' "$duplicate_log_names" >&2
                        exit 2
                fi
                # Opening a retained log must never truncate a selected input.
                # Compare file identity as well as spelling: the logging directory
                # or an existing destination can reach an input through a link.
                for name in "${log_names[@]}"; do
                        for destination in "$logdir/$name.log" "$logdir/$name.err"; do
                                [ -e "$destination" ] || continue
                                for path in "${paths[@]}"; do
                                        if [ "$destination" -ef "$path" ]; then
                                                printf 'log destination aliases benchmark input: %s (%s)\n' "$destination" "$path" >&2
                                                exit 2
                                        fi
                                done
                        done
                done
        fi
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
        xargs -0 -P "$para" -n 2 "$0" --xargs <"$RB_TMP/jobs" &
        RB_XARGS=$!
        wait "$RB_XARGS"
        exit $?
fi

elapsed_total() {
        local s=$(( $($date +%s) - RB_START ))
        printf '%02d:%02d:%02d' $((s / 3600)) $((s % 3600 / 60)) $((s % 60))
}

index=$2
shift
RB_OUTPUT=$(mktemp "${RB_DONE%/*}/output.XXXXXX") || exit $?
RB_GROUP=
RB_CONVERTED=
RB_CAPTURE_GROUP=
RB_CAPTURE_EVENT_FD=
RB_CAPTURE_HOLD_FD=
RB_CAPTURE_EVENT="$RB_OUTPUT.capture-event"
RB_CAPTURE_HOLD="$RB_OUTPUT.capture-hold"

# Each run is the process group of its `timeout`, which makes itself a group leader (GNU
# timeout does unless --foreground), so the solver and group-preserving descendants
# are in it. An escaped writer is not owned; closing our capture readers bounds
# waiting for its output without claiming to terminate that writer.
# The worker signals the solver group on a signal to the worker, and after the
# solver has exited, to stop whatever it left behind.  `kill` reaches the group while the
# timeout's pid is held, by the group's live members or by the unreaped process, so it cannot
# have been reused.
stop_group() {
        local group=$RB_GROUP i
        [ -n "$group" ] || return 0
        kill -TERM -- "-$group" "$group" 2>/dev/null
        for i in 1 2 3 4 5; do
                kill -0 -- "-$group" 2>/dev/null || break
                sleep 0.05
        done
        kill -KILL -- "-$group" 2>/dev/null
}
stop_capture() {
        if [ -n "$RB_CAPTURE_GROUP" ]; then
                # The positive PID also covers startup before timeout creates its group.
                kill -KILL -- "-$RB_CAPTURE_GROUP" "$RB_CAPTURE_GROUP" 2>/dev/null
                wait "$RB_CAPTURE_GROUP" 2>/dev/null
                RB_CAPTURE_GROUP=
        fi
        if [ -n "$RB_CAPTURE_EVENT_FD" ]; then
                exec {RB_CAPTURE_EVENT_FD}>&-
                RB_CAPTURE_EVENT_FD=
        fi
        if [ -n "$RB_CAPTURE_HOLD_FD" ]; then
                exec {RB_CAPTURE_HOLD_FD}>&-
                RB_CAPTURE_HOLD_FD=
        fi
        rm -f -- "$RB_CAPTURE_EVENT" "$RB_CAPTURE_HOLD"
}
cleanup_worker() {
        stop_capture
        stop_group
        rm -f -- "$RB_OUTPUT" "$RB_OUTPUT.text" "$RB_OUTPUT.fifo" "$RB_OUTPUT.err" "$RB_OUTPUT.errfifo" "$RB_OUTPUT.errfifo.copy" \
                ${RB_CONVERTED:+"$RB_CONVERTED"}
}
trap cleanup_worker EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
echo "[$index/$RB_TOTAL] running $2 (elapsed $(elapsed_total))" 1>&2

progress() {
        echo >>"$RB_DONE"
        echo "[done $(wc -l <"$RB_DONE" | tr -d ' ')/$RB_TOTAL, elapsed $(elapsed_total)] $1" 1>&2
}

# Keep at most one MiB plus an overflow byte, but drain the pipe to EOF.
# A plain file redirection would lose that boundary.
capture_output() {
        head -c 1048577 || return $?
        cat > /dev/null
}

export -f capture_output

# Clock failure is not a deadline. Validate both status and bytes before arithmetic.
attempt_clock() {
        local stamp
        stamp=$($date +%s%N) || return $?
        [[ "$stamp" =~ ^[0-9]+$ && "${#stamp}" -le 19 ]] || return 1
        [[ "${#stamp}" -lt 19 || "$stamp" < 9223372036854775808 ]] || return 1
        printf '%s\n' "$stamp"
}

# attempt INPUT sets ret and capture_ret, and retains the last stderr error line.
# The capture supervisor owns every reader and stays alive on the hold FIFO
# after reporting completion. Its process group cannot be reused while the
# parent decides whether to accept output or terminate the readers.
attempt() {
        local fifo="$RB_OUTPUT.fifo" errfifo="$RB_OUTPUT.errfifo" name
        local attempt_start now elapsed remaining event read_status
        rm -f -- "$fifo" "$errfifo" "$errfifo.copy" "$RB_OUTPUT.err"
        mkfifo -- "$fifo" "$RB_CAPTURE_EVENT" "$RB_CAPTURE_HOLD" || exit $?
        exec {RB_CAPTURE_EVENT_FD}<>"$RB_CAPTURE_EVENT" || exit $?
        exec {RB_CAPTURE_HOLD_FD}<>"$RB_CAPTURE_HOLD" || exit $?
        name=$(basename -- "$input_path")
        if [ -z "$logdir" ]; then
                mkfifo -- "$errfifo" "$errfifo.copy" || exit $?
        fi
        timeout 0 bash -c '
                trap - EXIT INT TERM
                fifo=$1; errfifo=$2; output=$3; logdir=$4; name=$5
                event_fd=$6; hold_fd=$7
                if [ -n "$logdir" ]; then
                        (set -o pipefail; tee -- "$logdir/$name.log" <"$fifo" | capture_output >"$output") &
                        stdout_pid=$!
                else
                        (LC_ALL=C grep -a "^error: " <"$errfifo.copy" | tail -n 1 >"$output.err") &
                        errors_pid=$!
                        tee -- "$errfifo.copy" <"$errfifo" >&2 &
                        stderr_pid=$!
                        capture_output <"$fifo" >"$output" &
                        stdout_pid=$!
                fi
                wait "$stdout_pid"; status=$?
                if [ -z "$logdir" ]; then
                        wait "$stderr_pid" || status=1
                        wait "$errors_pid" || status=1
                fi
                printf "%s\n" "$status" >&"$event_fd"
                # Keep the supervising group leader alive until parent cleanup.
                IFS= read -r -u "$hold_fd"
                exit "$status"
        ' _ "$fifo" "$errfifo" "$RB_OUTPUT" "$logdir" "$name" "$RB_CAPTURE_EVENT_FD" "$RB_CAPTURE_HOLD_FD" &
        RB_CAPTURE_GROUP=$!
        attempt_start=$(attempt_clock) || exit $?
        if [ -n "$logdir" ]; then
                timeout -k "$kill_after" "$timeout" $cmd $options "$1" >"$fifo" 2>"$logdir/$name.err" &
        else
                timeout -k "$kill_after" "$timeout" $cmd $options "$1" >"$fifo" 2>"$errfifo" &
        fi
        RB_GROUP=$!
        wait "$RB_GROUP"
        ret=$?
        now=$(attempt_clock)
        capture_ret=$?
        if [ "$capture_ret" -eq 0 ]; then
                elapsed="0000000000$((10#$now - 10#$attempt_start))"
                elapsed="${elapsed:0:${#elapsed}-9}.${elapsed: -9}"
                if [ "$ret" -eq 137 ] && [ -n "$RB_LIMIT" ] &&
                        awk -v e="$elapsed" -v l="$RB_LIMIT" 'BEGIN { exit !(e + 0 >= l + 0) }'; then
                        record_event "$1" killed "$ret" "$elapsed" || exit $?
                        ret=124
                fi
                while :; do
                        if [ -z "$RB_LIMIT" ]; then
                                IFS= read -r -u "$RB_CAPTURE_EVENT_FD" event
                                read_status=$?
                        else
                                now=$(attempt_clock) || { capture_ret=1; break; }
                                remaining=$(awk -v l="$RB_LIMIT" -v n="$now" -v s="$attempt_start" '
                                        BEGIN { r=l-(n-s)/1e9; if (r<=0) print "0"; else if (r>2147483647) print "2147483647"; else printf "%.9f\n", r }') || { capture_ret=1; break; }
                                if [ "$remaining" = 0 ] || [ "$remaining" = 0.000000000 ]; then
                                        ret=124
                                        capture_ret=0
                                        break
                                fi
                                IFS= read -r -t "$remaining" -u "$RB_CAPTURE_EVENT_FD" event
                                read_status=$?
                        fi
                        if [ "$read_status" -eq 0 ]; then
                                if [[ "$event" =~ ^[0-9]+$ ]]; then capture_ret=$event; else capture_ret=1; fi
                                break
                        fi
                        if [ -n "$RB_LIMIT" ] && [ "$read_status" -gt 128 ]; then continue; fi
                        capture_ret=1
                        break
                done
        fi
        kill -KILL -- "-$RB_GROUP" 2>/dev/null
        RB_GROUP=
        stop_capture
        if [ -n "$logdir" ]; then
                LC_ALL=C grep -a '^error: ' -- "$logdir/$name.err" | tail -n 1 >"$RB_OUTPUT.err"
        fi
        rm -f -- "$fifo" "$errfifo" "$errfifo.copy"
}

# record_event PATH EVENT STATUS SECONDS: one line of the events file (see the header).
# Lines are short single writes, so concurrent workers do not interleave them.
# When enabled, a required record must succeed before retry or row publication.
record_event() {
        [ -n "$events" ] || return 0
        printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" >>"$events"
}

# refusal_reason: succeeds when the last attempt was a refusal -- exit status 1 with a
# line `error: <reason>` on stderr, the one shape in which the tool reports an input,
# a pairing or a query it does not handle -- and sets reason to that line's text made
# safe for the row's unquoted fourth field: printable ASCII only (anything else becomes
# `?`), a comma becomes `;`, a double quote `'`, at most 200 characters.  A crash
# (an uncaught exception exits 2, and its `Fatal error:` line does not begin the line
# with `error:`), a signal, any other status and a refusal-looking line on stdout are
# not refusals.
refusal_reason() {
        reason=
        [ "$ret" -eq 1 ] && [ -s "$RB_OUTPUT.err" ] || return 1
        reason=$(head -c 1024 -- "$RB_OUTPUT.err" | LC_ALL=C tr -d '\n' | LC_ALL=C tr '\t' ' ' |
                LC_ALL=C tr -c ' -~' '?' | LC_ALL=C tr ',"' ";'")
        reason=${reason#error: }
        reason=${reason:0:200}
        return 0
}

elapsed_since() {
        local end_time delta
        end_time=$(attempt_clock) || return $?
        delta=$((10#$end_time - 10#$1))
        [ "$delta" -ge 0 ] || return 1
        printf '%d.%09d\n' "$((delta / 1000000000))" "$((delta % 1000000000))"
}

# run_optpcsat RETRIES PATH: OptPCSat answers over several lines; its verdict is the last
# line naming one, and its rows keep the shape the OptPCSat evaluation reads.
run_optpcsat() {
        start_time=$(attempt_clock) || exit $?
        attempt "$solver_input"
        output=""
        result=""
        iterations=""
        output_clean=false
        capture_size=$(wc -c <"$RB_OUTPUT")
        # Progress may span lines, but byte corruption anywhere in the capture
        # must not disappear during selection or Bash command substitution.
        if [ "$capture_ret" -eq 0 ] && [ "$capture_size" -le 1048576 ] &&
                LC_ALL=C tr -d '\000' <"$RB_OUTPUT" >"$RB_OUTPUT.text" &&
                cmp -s "$RB_OUTPUT" "$RB_OUTPUT.text"; then
                output=$(grep -a -E "Maxsat|Sat|Unknown|Unsat|MaxsatInSpace" "$RB_OUTPUT.text" | tail -n 1)
                IFS="," read -r result iterations <<<"$output"
                if [[ "$result" != *'"'* && "$result" != *$'\r'* &&
                        "$iterations" != *','* && "$iterations" != *'"'* &&
                        "$iterations" != *$'\r'* ]]; then
                        output_clean=true
                fi
        fi
        if [ "$ret" -eq 124 ] && [ "$output_clean" = true ] && [ -n "$RB_LIMIT" ]; then
                progress "$2: $result,timeout"
                printf '%s,%s,timeout,%s\n' "$2" "$result" "$iterations"
                exit
        fi
        elapsed=$(elapsed_since "$start_time") || exit $?
        if [ "$ret" -ne 0 ] || [ "$output_clean" != true ]; then
                result=""
                iterations=""
        fi
        case $result in
        valid | invalid | sat | unsat | unknown | infeasible | YES | NO | Sat | Maxsat | MaxsatInSpace | Unsat | Unknown | MAYBE)
                progress "$2: $output (${elapsed}s)"
                printf '%s,%s,%s,%s\n' "$2" "$result" "$elapsed" "$iterations"
                ;;
        *)
                if [ "$1" -gt 0 ]; then
                        echo "$2 Abort, restart! (status $ret)" 1>&2
                        record_event "$2" restart "$ret" "$elapsed" || exit $?
                        run_optpcsat $(($1 - 1)) "$2"
                else
                        iterations=""
                        progress "$2: abort (${elapsed}s)"
                        printf '%s,Sat(Abort),%s,%s\n' "$2" "$elapsed" "$iterations"
                fi
                ;;
        esac
}

run() {
        start_time=$(attempt_clock) || exit $?
        attempt "$solver_input"

        # Exit 124 is a timeout only when a deadline was set; with a zero limit
        # it can only come from the command itself and is treated as a failure.
        if [ "$ret" -eq 124 ] && [ "$capture_ret" -eq 0 ] && [ -n "$RB_LIMIT" ]; then
                progress "$2: timeout"
                printf '%s,timeout,%s\n' "$2" "$RB_LIMIT"
                exit
        fi

        # Bash substitutions discard NULs and trailing newlines. Validate the
        # original bytes first, then retain exactly one optional final LF.
        output=""
        output_clean=false
        capture_size=$(wc -c <"$RB_OUTPUT")
        if [ "$capture_ret" -eq 0 ] && [ "$capture_size" -le 1048576 ] &&
                LC_ALL=C tr -d '\000' <"$RB_OUTPUT" >"$RB_OUTPUT.text" &&
                cmp -s "$RB_OUTPUT" "$RB_OUTPUT.text" &&
                output=$(cat "$RB_OUTPUT.text" && printf '.'); then
                output=${output%.}
                output=${output%$'\n'}
                output_clean=true
        fi
        # The verdict is the first comma-separated field of the first line of stdout; what
        # follows it on that line is metadata, kept in the row's unquoted fourth field.
        # Accepted metadata: none, text with no comma, quote, tab or carriage return
        # (`sat,3`), MuVal's `<iterations>,<primal>|<dual>` (its one comma gives the fifth
        # column the result readers expect; they accept two to five columns), and RCaml's
        # `<iterations>   \t@assert <type> [#k]`, whose asserted type may contain commas
        # (`(u:unit,v:int list) => ...`): only its leading count is kept.  Any other
        # metadata, which would add fields, quote them or end the record, makes the run
        # untrusted.  MuVal's QFL answers (`-p qfl`) are `<verdict>, <seconds>s, <solution>`, whose
        # solution may contain commas: the metadata is accepted and nothing of it is kept, since
        # the row has its own time and the solution belongs in a log (logdir).  Later lines are accepted only as further answer lines with the same
        # verdict (RCaml prints one per assertion); anything else after the answer -- an
        # error a process the solver started still writes, an empty line -- is not.  One
        # exception: `-p smt` prints a satisfiable answer as a bare `sat` and then one line
        # `model: ...` (empty for a stochastic problem), so that line, as the second line
        # after a bare `sat`, is part of the answer; it never enters the row.
        first_line=${output%%$'\n'*}
        result=${first_line%%,*}
        metadata=
        [[ "$first_line" == *','* ]] && metadata=${first_line#*,}
        answer_ok=true
        rcaml_metadata=$'^([0-9]+) *\t@assert '
        qfl_metadata='^ [0-9]+(\.[0-9]+)?s(, .*)?$'
        if [[ "$metadata" =~ ^[0-9]+,[0-9]+\|[0-9]+$ ]] ||
                [[ "$metadata" != *[,\"$'\r\t']* ]]; then
                iterations=$metadata
        elif [[ "$metadata" =~ $rcaml_metadata && "$metadata" != *$'\r'* ]]; then
                iterations=${BASH_REMATCH[1]}
        elif [[ "$metadata" =~ $qfl_metadata && "$metadata" != *[$'\r\t']* ]]; then
                iterations=
        else
                iterations=
                answer_ok=false
        fi
        if [[ "$output" == *$'\n'* ]]; then
                local later=0
                while IFS= read -r line; do
                        later=$((later + 1))
                        if [ "$later" -eq 1 ] && [ "$first_line" = sat ] &&
                                [[ "$line" == 'model:'* && "$line" != *$'\r'* ]]; then
                                continue
                        fi
                        if [[ "$line" != "$result",* || "$line" == *$'\r'* ]]; then
                                answer_ok=false
                        fi
                done <<<"${output#*$'\n'}"
        fi

        elapsed=$(elapsed_since "$start_time") || exit $?

        # `timeout` is an answer the solver prints itself when its own budget runs out
        # (exit 0, `timeout,<iterations>`): it is a timeout, not an abort, so a refusal, a
        # crash and a timeout stay apart; its row carries the elapsed time, a limit row
        # (the deadline's exit 124, above) the limit.  A refusal is retried like an abort
        # (so the number of runs is what it was), and when the last attempt refused, its
        # row is `refused` with the reason in the fourth field instead of `abort`.
        # The fourth CSV field is unquoted: the selection above decided what may enter it.
        if [ "$ret" -eq 0 ] && [ "$output_clean" = true ] && [ "$answer_ok" = true ] &&
                { [ "$result" = "valid" ] ||
                [ "$result" = "invalid" ] ||
                [ "$result" = "sat" ] ||
                [ "$result" = "unsat" ] ||
                [ "$result" = "unknown" ] ||
                [ "$result" = "infeasible" ] ||
                [ "$result" = "timeout" ] ||
                [ "$result" = "YES" ] ||
                [ "$result" = "NO" ] ||
                [ "$result" = "MAYBE" ]; }; then
                progress "$2: ${output%%$'\n'*} (${elapsed}s)"
                printf '%s,%s,%s,%s\n' "$2" "$result" "$elapsed" "$iterations"
        elif [ "$1" -gt 0 ]; then
                echo "$2 Abort, restart! (status $ret)" 1>&2
                record_event "$2" restart "$ret" "$elapsed" || exit $?
                run $(( $1 - 1 )) "$2"
        elif refusal_reason; then
                progress "$2: refused: $reason (${elapsed}s)"
                printf '%s,refused,%s,%s\n' "$2" "$elapsed" "$reason"
        else
                # Failed output is untrusted, including its metadata.
                iterations=""
                progress "$2: abort (${elapsed}s)"
                printf '%s,abort,%s,%s\n' "$2" "$elapsed" "$iterations"
        fi
}

input_path=$2
solver_input=$2
if [ -n "$convert" ]; then
        # Conversion belongs to this worker, including when input basenames repeat.
        solver_input="$RB_OUTPUT.smt2"
        RB_CONVERTED=$solver_input
        if _build/default/main.exe -c ./config/solver/printer_smt2.json -p "${convert#smt2:}" "$2" >"$solver_input"; then
                :
        else
                convert_ret=$?
                printf '%s: SMT-LIB conversion failed (exit %s)\n' "$2" "$convert_ret" >&2
                exit "$convert_ret"
        fi
fi
if [ "$reader" = optpcsat ]; then
        run_optpcsat "$retries" "$2"
else
        run "$retries" "$2"
fi
