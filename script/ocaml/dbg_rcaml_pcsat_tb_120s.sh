#! /bin/bash

mkdir -p $2
for file in $1/*
do
    if test -f $file
    then
        file_name=`basename $file ".ml"`
        echo $file_name
        dune exec main -- -c ./config/solver/dbg_rcaml_pcsat_tb_120s.json -p ml $file &> $2/$file_name.log
    fi
done
