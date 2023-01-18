pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause and with UBs eps0):"
./script/popl2023mod/muval_parallel_exc_eps0_tb_ar.sh >./popl2023mod_parallel_exc_eps0_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause and with UBs eps1):"
./script/popl2023mod/muval_parallel_exc_eps1_tb_ar.sh >./popl2023mod_parallel_exc_eps1_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause and with UBs eps2):"
./script/popl2023mod/muval_parallel_exc_eps2_tb_ar.sh >./popl2023mod_parallel_exc_eps2_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause and with LBs):"
./script/popl2023mod/muval_parallel_exc_tb_ar_lbs.sh >./popl2023mod_parallel_exc_tb_ar_lbs_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause):"
./script/popl2023mod/muval_parallel_exc_tb_ar.sh >./popl2023mod_parallel_exc_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel:"
./script/popl2023mod/muval_parallel_tb_ar.sh >./popl2023mod_parallel_tb_ar_$1.csv
pkill -9 main
sleep 0.1
# echo "call tb ar parallel (exchange_learned_clause eps0):"
# ./script/popl2023mod/muval_parallel_exc_eps0_tb_ar.sh >./popl2023mod_parallel_exc_eps0_tb_ar_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel (exchange_learned_clause eps1):"
# ./script/popl2023mod/muval_parallel_exc_eps1_tb_ar.sh >./popl2023mod_parallel_exc_eps1_tb_ar_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel (exchange_learned_clause eps2):"
# ./script/popl2023mod/muval_parallel_exc_eps2_tb_ar.sh >./popl2023mod_parallel_exc_eps2_tb_ar_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel_nonopt (exchange_learned_clause):"
# ./script/popl2023mod/muval_parallel_nonopt_exc_tb_ar.sh >./popl2023mod_parallel_nonopt_tb_ar_exc_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel_nonopt:"
# ./script/popl2023mod/muval_parallel_nonopt_tb_ar.sh >./popl2023mod_parallel_nonopt_tb_ar_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel (exchange_learned_clause):"
# ./script/popl2023mod/muval_parallel_exc_tb.sh >./popl2023mod_parallel_exc_tb_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel:"
# ./script/popl2023mod/muval_parallel_tb.sh >./popl2023mod_parallel_tb_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel_nonopt (exchange_learned_clause):"
# ./script/popl2023mod/muval_parallel_nonopt_exc_tb.sh >./popl2023mod_parallel_nonopt_exc_tb_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel_nonopt:"
# ./script/popl2023mod/muval_parallel_nonopt_tb.sh >./popl2023mod_parallel_nonopt_tb_$1.csv
# pkill -9 main
# sleep 0.1
