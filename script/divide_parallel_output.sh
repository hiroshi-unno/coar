
fname=`basename $1`
cat $1 | grep "\[#1\]" > $fname.1
cat $1 | grep "\[#2\]" > $fname.2