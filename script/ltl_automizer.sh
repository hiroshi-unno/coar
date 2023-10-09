#!/bin/bash

## run this file at folder of ultimate_ltl_automizer

is_mac() {
    sw_vers > /dev/null 2>&1
    return $?
}

if is_mac; then
    date='gdate'
else
    date='date'
fi

if [ -z "$2" ]; then
    echo "E.g: $0 [src_dir] [log file target dir]"
    exit
fi
if [ -f $1 ]; then
    echo "$1 is not a director."
    exit
fi
timelimit=300
run() {
    if [ ! -d $2 ]; then
        mkdir $2
    fi
    for file in $1/*; do
        fname=$(basename $file)
        if [ -f $1/$fname ]; then
            start_time=$($date +%s%N)
            output=$(timeout $timelimit ./Ultimate LTLAutomizerC.xml $file --settings Default.epf)
            ret=$?
            end_time=$($date +%s%N)
            elapsed="0000000000$((end_time - start_time))"
            elapsed=$(sed -E 's/(.{9})$/.\1/' <<<"$elapsed" | sed -E 's/^0*([^0]*.)\./\1./')
            echo "${output}" >$2/$fname.log
            if [ $ret = 124 ]; then
                echo "$file,timeout,$elapsed"
            else
                invalid=$(echo $output | grep "violates the LTL property")
                if [ -z "$invalid" ]; then
                    echo "$file,YES,$elapsed"
                else
                    echo "$file,NO,$elapsed"
                fi
            fi
        fi
        if [ -d $1/$fname ]; then
            run $1/$fname $2/$fname
        fi
    done
}

run $1 $2
