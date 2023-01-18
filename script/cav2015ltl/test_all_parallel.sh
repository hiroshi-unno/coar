./script/cav2015ltl/muval_script_tb_ar.sh > ./cav2015ltl_script_tb_ar_$1.csv
./script/cav2015ltl/muval_script_tb.sh > ./cav2015ltl_script_tb_$1.csv
./script/cav2015ltl/muval_script_nu_tb_ar.sh > ./cav2015ltl_script_nu_tb_ar_$1.csv
./script/cav2015ltl/muval_script_nu_tb.sh > ./cav2015ltl_script_nu_tb_$1.csv


pkill -9 main
sleep 0.1
echo "call tb ar parallel (exchange_learned_clause):"
./script/cav2015ltl/muval_parallel_exc_tb_ar.sh > ./cav2015ltl_parallel_exc_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel:"
./script/cav2015ltl/muval_parallel_tb_ar.sh > ./cav2015ltl_parallel_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb parallel (exchange_learned_clause):"
./script/cav2015ltl/muval_parallel_exc_tb.sh > ./cav2015ltl_parallel_exc_tb_$1.csv
pkill -9 main
sleep 0.1
echo "call tb parallel:"
./script/cav2015ltl/muval_parallel_tb.sh > ./cav2015ltl_parallel_tb_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar nu parallel:"
./script/cav2015ltl/muval_parallel_nu_tb_ar.sh > ./cav2015ltl_parallel_nu_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb nu parallel:"
./script/cav2015ltl/muval_parallel_nu_tb.sh > ./cav2015ltl_parallel_nu_tb_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel_nonopt (exchange_learned_clause):"
./script/cav2015ltl/muval_parallel_exc_nonopt_tb_ar.sh > ./cav2015ltl_parallel_exc_nonopt_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb ar parallel_nonopt:"
./script/cav2015ltl/muval_parallel_nonopt_tb_ar.sh > ./cav2015ltl_parallel_nonopt_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call tb parallel_nonopt (exchange_learned_clause):"
./script/cav2015ltl/muval_parallel_exc_nonopt_tb.sh > ./cav2015ltl_parallel_exc_nonopt_tb_$1.csv
pkill -9 main
sleep 0.1
echo "call tb parallel_nonopt:"
./script/cav2015ltl/muval_parallel_nonopt_tb.sh > ./cav2015ltl_parallel_nonopt_tb_$1.csv
pkill -9 main
sleep 0.1
