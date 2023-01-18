# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel (exchange_learned_clause):"
# ./script/termcomp20cint/muval_parallel_exc_tb_ar.sh >./termcomp20cint_tb_ar_parallel_exc_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb ar parallel:"
# ./script/termcomp20cint/muval_parallel_tb_ar.sh >./termcomp20cint_tb_ar_parallel_$1.csv
# pkill -9 main
# sleep 0.1
echo "call tb ar parallel_nonopt (exchange_learned_clause):"
./script/termcomp20cint/muval_parallel_exc_nonopt_tb_ar.sh >./termcomp20cint_tb_ar_parallel_exc_nonopt_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel_nonopt:"
./script/termcomp20cint/muval_parallel_nonopt_tb_ar.sh >./termcomp20cint_tb_ar_parallel_nonopt_$1.csv
pkill -9 main
sleep 0.1
# echo "call tb parallel (exchange_learned_clause):"
# ./script/termcomp20cint/muval_parallel_exc_tb.sh >./termcomp20cint_tb_parallel_exc_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel:"
# ./script/termcomp20cint/muval_parallel_tb.sh >./termcomp20cint_tb_parallel_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel_nonopt (exchange_learned_clause):"
# ./script/termcomp20cint/muval_parallel_exc_nonopt_tb.sh >./termcomp20cint_tb_parallel_exc_nonopt_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call tb parallel_nonopt:"
# ./script/termcomp20cint/muval_parallel_nonopt_tb.sh >./termcomp20cint_tb_parallel_nonopt_$1.csv
# pkill -9 main
# sleep 0.1
