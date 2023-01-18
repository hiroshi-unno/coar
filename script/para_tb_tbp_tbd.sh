#!/bin/bash

#rm output
#mkfifo output
(./script/para_aux.sh $timeout ./_build/default/main.exe -c ./config/solver/pcsat_tb.json $options $1 > output1) &
pid1=$!
(./script/para_aux.sh $timeout ./_build/default/main.exe -c ./config/solver/muval_prove_tb.json $options $1 > output2) &
pid2=$!
(./script/para_aux.sh $timeout ./_build/default/main.exe -c ./config/solver/muval_disprove_tb.json $options $1 > output3) &
pid3=$!

while :
do
    alive1=`ps -ef | grep " $pid1 " | grep -v grep | awk '{ print $2 }'`
    alive2=`ps -ef | grep " $pid2 " | grep -v grep | awk '{ print $2 }'`
    alive3=`ps -ef | grep " $pid3 " | grep -v grep | awk '{ print $2 }'`
    if [ -z "$alive1" ] && [ -z "$alive2" ] && [ -z "$alive3" ]; then
        cat output1
        break
    fi

    if [ -z  "$alive1" ] && [ -z "$alive2" ] && ["$alive3"]; then
#        echo "kill3"
        kill $pid3
        cat output1
        break
    fi

    if [ -z "$alive1" ] && [ "$alive2" ] && [ -z "$alive3"]; then
#        echo "kill2"
        kill $pid2
        cat output1
        break
    fi

    if [ -z  "$alive1" ] && [ "$alive2" ] && ["$alive3"]; then
#        echo "kill2 3"
        kill $pid2
        kill $pid3
        cat output1
        break
    fi

    if [ "$alive1" ] && [ -z "$alive2" ] && [ -z "$alive3"]; then
#        echo "kill1"
        kill $pid1
        cat output2
        break
    fi
    
    if [  "$alive1" ] && [ -z "$alive2" ] && ["$alive3"]; then
#        echo "kill1 3"
        kill $pid1
        kill $pid3
        cat output2
        break
    fi
    
    if ["$alive1" ] && [ "$alive2" ] && [ -z  "$alive3"]; then
#        echo "kill1 2"
        kill $pid2
        kill $pid1
        cat output3
        break
    fi
#    echo "still run"
    sleep 0.1
done
