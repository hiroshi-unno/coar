pkill -9 main
sleep 0.1
echo "call tb ar nu parallel:"
./script/popl2023mod/muval_parallel_nu_tb_ar.sh >./popl2023mod_parallel_nu_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb nu parallel:"
./script/popl2023mod/muval_parallel_nu_tb.sh >./popl2023mod_parallel_nu_tb_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar nu script:"
./script/popl2023mod/muval_script_nu_tb_ar.sh >./popl2023mod_script_nu_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb nu script:"
./script/popl2023mod/muval_script_nu_tb.sh >./popl2023mod_script_nu_tb_$1.csv
pkill -9 main
sleep 0.1
