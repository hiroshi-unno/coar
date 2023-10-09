#!/bin/bash

#find $@ | xargs -n 1 ./para_dtp_dtd.sh 2> /dev/null

#buf=""
for file in `find $@`; do
    echo -n "|" 1>&2
    echo `./script/para_dtp_dtd.sh $file 2> /dev/null`
#    buf=$buf"\n"`./para_dtp_dtd.sh $file 2> /dev/null`
done
echo "" 1>&2
#LC_ALL=C
#echo $buf | sort
