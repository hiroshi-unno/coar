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

        find $@ | xargs -P 1 -n 1 $0 --xargs
        exit
fi

# dune build main.exe

run() {
        start_time=$($date +%s%N)
        output=$(timeout $timeout _build/default/main.exe $options $2)
        ret=$?
        pkill -9 main 2> /dev/null
        sleep 0.1

        output=$(echo "$output" | grep -E "Maxsat|Sat|Unknown|Unsat|MaxsatInSpace" | tail -n 1)
        IFS="," read result iterations <<<"$output"
        if [ $ret = 124 ]; then
                echo "solved $2:$result,timeout,$iterations" 1>&2
                echo "$2,$result,timeout,$iterations"
                exit
        fi

        end_time=$($date +%s%N)
        elapsed="0000000000$((end_time - start_time))"
        elapsed=$(sed -E 's/(.{9})$/.\1/' <<<"$elapsed" | sed -E 's/^0*([^0]*.)\./\1./')
        intseconds=$(echo $elapsed | cut -d '.' -f1)

        if [ "$result" = "valid" ] ||
                [ "$result" = "invalid" ] ||
                [ "$result" = "sat" ] ||
                [ "$result" = "unsat" ] ||
                [ "$result" = "unknown" ] ||
                [ "$result" = "infeasible" ] ||
                [ "$result" = "YES" ] ||
                [ "$result" = "NO" ] ||
                [ "$result" = "Maxsat" ] ||
                [ "$result" = "MaxsatInSapce" ] ||
                [ "$result" = "Unsat" ] ||
                [ "$result" = "Unknown" ] ||
                [ "$result" = "MAYBE" ]; then
                echo "solved $2,$elapsed,$output" 1>&2
                echo "$2,$result,$elapsed,$iterations"
        elif [ $1 -gt 0 ]; then
                # echo "$2 Abort, restart!" 1>&2
                pkill -9 main 2> /dev/null
                sleep 0.1
                run $(expr $1 - 1) $2
        else
                echo "solved $2,$elapsed,Sat(Abort)" 1>&2
                echo "$2,Sat(Abort),$elapsed,$iterations"
        fi
}

run 12 $2
