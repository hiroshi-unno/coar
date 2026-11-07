#!/bin/bash

is_mac () {
  sw_vers > /dev/null 2>&1
  return $?
}

if is_mac ; then
       date='gdate'
else
       date='date'
fi

# Note that timeout changes its process group, so timeout cannot recieve SIGINT from a terminal.
# Note also that when ocaml invokes z3, SIGINT terminates not the whole program but just z3.
function interruptible_timeout() {
	timeout $@ &
	pid=$!
	trap "kill -TERM -$pid" INT
	wait $pid
}

function nanosec2sec() {
	sed -E 's/(.{9})$/.\1/' <<< "$1" | sed -E 's/^0*(0|([1-9][0-9]*))\./\1./'
}

# stderr is kept in a file and replayed after the run, so that a refusal (status 1 and a
# last stderr line `error: <reason>`) can be told apart from a crash.
errfile=$(mktemp) || exit $?
trap 'rm -f -- "$errfile"' EXIT
start_time=$($date +%s%N)
output=`interruptible_timeout $@ 2>"$errfile"`
status=$?
cat -- "$errfile" >&2

if [ $status = 124 ]; then
	end_time=$($date +%s%N)
	elapsed=$(nanosec2sec "0000000000$((end_time - start_time))")
    echo "${@:$#:1},timeout,$elapsed"
    exit
fi

IFS="," read result iterations <<< "$output"

end_time=$($date +%s%N)
elapsed=$(nanosec2sec "0000000000$((end_time - start_time))")

if      [ "$result" = "valid" ] ||
        [ "$result" = "invalid" ] ||
        [ "$result" = "sat" ] ||
        [ "$result" = "unsat" ] ||
        [ "$result" = "unknown" ] ||
        [ "$result" = "infeasible" ] ||
        [ "$result" = "YES" ] ||
        [ "$result" = "NO" ] ||
        [ "$result" = "MAYBE" ]; then

        echo "${@:$#:1},$result,$elapsed,$iterations"
elif [ $status = 1 ] && reason=$(LC_ALL=C grep -a '^error: ' -- "$errfile" | tail -n 1) && [ -n "$reason" ]; then
        # The reason enters an unquoted CSV field: printable ASCII, no comma or quote.
        reason=$(printf '%s' "${reason#error: }" | LC_ALL=C tr '\t' ' ' | LC_ALL=C tr -c ' -~' '?' | LC_ALL=C tr ',"' ";'")
        echo "${@:$#:1},refused,$elapsed,${reason:0:200}"
else
        echo "${@:$#:1},abort,$elapsed,$iterations"
fi

