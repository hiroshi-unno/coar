pkill -9 main
sleep 0.1
echo "call maxchc_nc_tb_ar_fix1:"
./script/popl2023opt/maxchc_nc_tb_ar_fix1.sh >./popl2023opt_maxchc_nc_tb_ar_fix1_$1.csv
pkill -9 main
sleep 0.1
echo "call maxchc_nc_tb_ar_fix2:"
./script/popl2023opt/maxchc_nc_tb_ar_fix2.sh >./popl2023opt_maxchc_nc_tb_ar_fix2_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call maxchc_nc_tb_ar_fix1_interval3:"
# ./script/popl2023opt/maxchc_nc_tb_ar_fix1_interval3.sh >./popl2023opt_maxchc_nc_tb_ar_fix1_interval3_$1.csv
# pkill -9 main
# sleep 0.1
# echo "call maxchc_nc_tb_ar_fix2_interval3:"
# ./script/popl2023opt/maxchc_nc_tb_ar_fix2_interval3.sh >./popl2023opt_maxchc_nc_tb_ar_fix2_interval3_$1.csv
