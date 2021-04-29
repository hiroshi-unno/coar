#!/bin/bash

if [ "$1" != "--xargs" ]; then
        if [ -z "$timeout" ]; then
                echo "e.g., timeout=10 ... $0"
                exit
        fi

        if [ -z "$options" ]; then
                echo "e.g., options='--synthesizer tb' ... $0"
                exit
        fi

        find $@ | xargs -P 8 -n 1 $0 --xargs
        exit
fi

output=`python3 ./prove_and_disprove.py $timeout "$options" $2`

#IFS="," read result iterations <<< "$output"

echo "$output"
