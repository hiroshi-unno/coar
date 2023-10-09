#!/bin/bash

killtree=./script/killtree.sh
LLVM2KITTEL=~/llvm2kittel/build/llvm2kittel
CLANG=clang

#INPUT=$(basename $1 ".c")
BCFILE=$(mktemp --suffix=.bc)
T2FILE=$(mktemp --suffix=.t2)

$CLANG -c -emit-llvm -O0 $1 -o ${BCFILE} 2> /dev/null
$LLVM2KITTEL --dump-ll --no-slicing --eager-inline --t2 ${BCFILE} > ${T2FILE}

#rm output
#mkfifo output
output1=$(mktemp)
output2=$(mktemp)
(./script/para_aux.sh $timeout ./_build/default/main.exe -c $prove_config $options $T2FILE > $output1) &
#(./script/para_aux.sh $timeout ./_build/default/main.exe -c $prove_config $options $1 > $output1) &
pid1=$!
(./script/para_aux.sh $timeout ./_build/default/main.exe -c $disprove_config $options $T2FILE > $output2) &
#(./script/para_aux.sh $timeout ./_build/default/main.exe -c $disprove_config $options $1 > $output2) &
pid2=$!
trap "kill 0" INT
trap "rm $T2FILE $BCFILE $output1 $output2" EXIT

# replace $T2FILE to $1 (original c file)
PATTERN=s/$(echo $T2FILE | sed -e 's/\//\\\//g')/$(echo $1 | sed -e 's/\//\\\//g')/g

while :
do
    alive1=$(ps -ef | grep " $pid1 " | grep -v grep | awk '{ print $2 }')
    alive2=$(ps -ef | grep " $pid2 " | grep -v grep | awk '{ print $2 }')
    if [ -z "$alive1" ] && [ -z "$alive2" ]; then
		sed -e $PATTERN $output1
        break
    fi

    if [ -z "$alive1" ] && [ "$alive2" ]; then
        $killtree $pid2
		sed -e $PATTERN $output1
        break
    fi

    if [ "$alive1" ] && [ -z "$alive2" ]; then
        $killtree $pid1
		sed -e $PATTERN $output2
        break
    fi
    sleep 0.1
done

