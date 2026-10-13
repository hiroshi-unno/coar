
#$1: object folder
bin_path=$1/bin
mkdir -p $bin_path
folder_name=${1##*/}
zip_name=$folder_name.zip
ldd ./_build/default/main.exe | while read line; do
    temp=${line##*'=>'}
    path=${temp%' (0x'*}
    fname=`basename $path`
    cp $path $bin_path
    chmod 777 $bin_path/$fname
    echo 'copying from' $path 'to' $bin_path/$fname
done
cp ./_build/default/main.exe $bin_path/
chmod 777 $bin_path/main.exe
cd $1
rm $zip_name
zip -r $zip_name bin *.txt