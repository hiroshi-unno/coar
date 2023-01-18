if [ -z "$2" ]; then
        echo "E.g: $0 [src_dir or src_file] [dst_dir]"
        exit
fi

if [ ! -d $2 ]; then
    mkdir $2
fi
echo generate $1
if [ -f $1 ]; then 
    fname=`basename $1` 
    _build/default/main.exe -c ./config/solver/printer.json -p cctl $1 > $2/$fname.hes
    echo "testing $2/$fname.hes"
    _build/default/main.exe -c ./config/solver/printer.json -p muclp $2/$fname.hes 1> /dev/null
fi
for file_a in $1/* 
do  
    fname=`basename $file_a`  
    if [ -f $1/$fname ]; then 
        _build/default/main.exe -c ./config/solver/printer.json -p cctl $1/$fname > $2/$fname.hes
        echo "testing $2/$fname.hes"
        _build/default/main.exe -c ./config/solver/printer.json -p muclp $2/$fname.hes 1> /dev/null
    fi
    if [ -d $1/$fname ]; then 
        sh $0 $1/$fname $2/$fname
    fi
done