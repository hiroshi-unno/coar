#!/bin/bash

COL_TIME=5
COL_ANS=10

tmpfile=$(mktemp)

function get_column() {
	echo $2 | cut -d , -f $1
}

while read line
do
	FILENAME=$(get_column 1 $line)
	FILENAME=$(basename $(dirname $FILENAME))/$(basename $FILENAME)
	ANS=$(get_column 2 $line | sed -e 's/timeout/MAYBE/')
	TIME=$(get_column 3 $line)
	EXPECTED_RESULT=$(grep $FILENAME cav21ae_dt/term-comp20.csv)
	if [ "$ANS" != "$(get_column $COL_ANS $EXPECTED_RESULT)" ]; then
		echo "$FILENAME: $(get_column $COL_ANS $EXPECTED_RESULT) on starexec, $ANS on local"
	fi
	echo $TIME,$(get_column $COL_TIME $EXPECTED_RESULT) >> $tmpfile
done < $1

SCATTERPLOT=compare_eager.eps

gnuplot << EOS
set size square
set terminal postscript eps enhanced color
set output '$SCATTERPLOT'
set datafile separator ","
set xr[0.2:305]
set yr[0.2:305]
# set border 3
set border back
set xlabel font "Helvetica,30"
set ylabel font "Helvetica,30"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'local'
set ylabel 'starexec'
plot x lc rgb "black" notitle, '$tmpfile' u 1:2 notitle pt 7 lc rgb "red"
EOS

rm $tmpfile
