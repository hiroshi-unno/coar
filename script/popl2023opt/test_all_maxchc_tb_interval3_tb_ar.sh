pkill -9 main
sleep 0.1
echo "call maxchc_nc_tb_interval3_tb_ar:"
./script/popl2023opt/maxchc_nc_tb_interval3_tb_ar.sh >./popl2023opt_maxchc_nc_tb_interval3_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call maxchc_nt_tb_interval3_tb_ar:"
./script/popl2023opt/maxchc_nt_tb_interval3_tb_ar.sh >./popl2023opt_maxchc_nt_tb_interval3_tb_ar_$1.csv
pkill -9 main
sleep 0.1
echo "call maxchc_nv_tb_interval3_tb_ar:"
./script/popl2023opt/maxchc_nv_tb_interval3_tb_ar.sh >./popl2023opt_maxchc_nv_tb_interval3_tb_ar_$1.csv
