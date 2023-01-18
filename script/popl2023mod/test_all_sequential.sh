pkill -9 main
sleep 0.1
echo "call tb ar prove:"
./script/popl2023mod/muval_prove_tb_ar.sh >./popl2023mod_prove_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar disprove:"
./script/popl2023mod/muval_disprove_tb_ar.sh >./popl2023mod_disprove_tb_ar_$1.csv
pkill -9 main
sleep 0.1
