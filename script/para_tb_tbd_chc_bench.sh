#!/bin/bash

#find $@ | xargs -n 1 ./para_tb_tbd.sh 2> /dev/null

#buf=""
for file in `find $@`; do
    echo -n "|" 1>&2
    echo `timeout=10 options='-p pcsp' ./script/para_tb_tbd.sh $file 2> /dev/null`
#    buf=$buf"\n"`./para_tb_tbd.sh $file 2> /dev/null`
done
echo "" 1>&2
#LC_ALL=C
#echo $buf | sort
