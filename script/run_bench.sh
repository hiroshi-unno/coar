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

if [ "$1" != "--xargs" ]; then
        if [ -z "$timeout" ]; then
                echo "e.g., timeout=10 ... $0"
                exit
        fi

        if [ -z "$options" ]; then
                echo "e.g., options='--synthesizer tb' ... $0"
                exit
        fi

        find $@ | xargs -P 3 -n 1 $0 --xargs
        exit
fi

# dune build main.exe

run() {
        start_time=$($date +%s%N)
        output=$(timeout $timeout _build/default/main.exe $options $2)
        ret=$?

        if [ $ret = 124 ]; then
                echo "solved $2:timeout" 1>&2
                echo "$2,timeout,"
                exit
        fi

        echo "solved $2:$output" 1>&2

        IFS="," read result iterations <<<"$output"

        end_time=$($date +%s%N)
        elapsed="0000000000$((end_time - start_time))"
        elapsed=$(sed -E 's/(.{9})$/.\1/' <<<"$elapsed" | sed -E 's/^0*([^0]*.)\./\1./')

        if [ "$result" = "valid" ] ||
                [ "$result" = "invalid" ] ||
                [ "$result" = "sat" ] ||
                [ "$result" = "unsat" ] ||
                [ "$result" = "unknown" ] ||
                [ "$result" = "infeasible" ] ||
                [ "$result" = "YES" ] ||
                [ "$result" = "NO" ] ||
                [ "$result" = "MAYBE" ]; then

                echo "$2,$result,$elapsed,$iterations"
        elif [$1 -gt 0]; then
                echo "$2 Abort, restart!" 1>&2
                run $(expr $1 - 1) $2
        else
                echo "solved $2,$elapsed,abort" 1>&2
                echo "$2,abort,$elapsed,$iterations"
        fi
}

run 1 $2
