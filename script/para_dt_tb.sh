#!/bin/bash

#rm output
#mkfifo output
(./script/para_aux.sh $timeout ./_build/default/main.exe -c ./config/solver/pcsat_dt.json $options $1 > output1) &
pid1=$!
(./script/para_aux.sh $timeout ./_build/default/main.exe -c ./config/solver/pcsat_tb.json $options $1 > output2) &
pid2=$!

while :
do
    alive1=`ps -ef | grep " $pid1 " | grep -v grep | awk '{ print $2 }'`
    alive2=`ps -ef | grep " $pid2 " | grep -v grep | awk '{ print $2 }'`
    if [ -z "$alive1" ] && [ -z "$alive2" ]; then
        cat output1
        break
    fi

    if [ -z "$alive1" ] && [ "$alive2" ]; then
#        echo "kill2"
        kill $pid2
        cat output1
        break
    fi

    if [ "$alive1" ] && [ -z "$alive2" ]; then
#        echo "kill1"
        kill $pid1
        cat output2
        break
    fi
#    echo "still run"
    sleep 0.1
done
