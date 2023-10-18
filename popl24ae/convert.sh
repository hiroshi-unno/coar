#!/bin/bash

cd $(dirname $0)

outfile_spacer="table_spacer.csv"
echo "file name, [Spacer] result correct?, [Spacer] time" > $outfile_spacer
cat results_spacer.csv | LC_ALL=C sort | while IFS=, read file answer time _; do
    file_name=$(basename $file)
    if [[ "$answer" == "timeout" ]]; then
        res="-"
        tim="timeout"
    elif [[ "$answer" == "(excluded)" ]]; then
        res="(excluded)"
        tim="-"
    elif [[ "$answer" == "unknown" || "$answer" == "abort" ]]; then
        res="abort"
        tim="-"
    elif [[ "$file_name" =~ "-${answer^^}" ]]; then # ^^ means "to uppercase"
        res="Yes"
        tim=$time
    else
        res="No"
        tim=$time
    fi
    echo "$file_name, $res, $tim" >> $outfile_spacer
done

outfile_pcsat="table_pcsat.csv"
echo "file name, [PCSat] result correct?, [PCSat] time" > $outfile_pcsat
cat results_pcsat.csv | LC_ALL=C sort | while IFS=, read file answer time _; do
    file_name=$(basename $file)
    if [[ "$answer" == "timeout" ]]; then
        res="-"
        tim="timeout"
    elif [[ "$answer" == "(excluded)" ]]; then
        res="(excluded)"
        tim="-"
    elif [[ "$answer" == "unknown" || "$answer" == "abort" ]]; then
        res="abort"
        tim="-"
    elif [[ "$file_name" =~ "-${answer^^}" ]]; then # ^^ means "to uppercase"
        res="Yes"
        tim=$time
    else
        res="No"
        tim=$time
    fi
    echo "$file_name, $res, $tim" >> $outfile_pcsat
done

outfile_cps="table_cps.csv"
echo "program, [DS] verified?, [DS] time, [CPS] verified?, [CPS] time, [CPS opt] verified?, [CPS opt] time" > $outfile_cps
cat results_cps.csv | LC_ALL=C sort | while true; do
    IFS=, read file_cps answer_cps time_cps _
    IFS=, read file_cpsopt answer_cpsopt time_cpsopt _
    IFS=, read file_ds answer_ds time_ds _

    if [ -z "$file_cps" ]; then break; fi

    file_name=$(basename $file_cps)
    prog=${file_name%_*} # delete suffix that matches "_*"

    function to_yesno() {
        if [[ "$1" == "sat" ]]; then
            echo "Yes"
        elif [[ "$1" == "unsat" ]]; then
            echo "No"
        else
            echo "$1"
        fi
    }
    res_ds=$(to_yesno $answer_ds)
    res_cps=$(to_yesno $answer_cps)
    res_cpsopt=$(to_yesno $answer_cpsopt)

    echo "$prog, $res_ds, $time_ds, $res_cps, $time_cps, $res_cpsopt, $time_cpsopt" >> $outfile_cps
done