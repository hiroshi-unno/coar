echo "START tb_ar_lustre" 1>&2
$(dirname $0)/tb_ar_lustre.sh > $1_lustre_tb_ar.csv
pkill -9 main 2> /dev/null
echo "START tb_lustre" 1>&2
$(dirname $0)/tb_lustre.sh > $1_lustre_tb.csv
pkill -9 main 2> /dev/null
echo "START spacer_lustre" 1>&2
$(dirname $0)/spacer_lustre.sh > $1_lustre_spacer.csv
pkill -9 main 2> /dev/null
echo "START eldarica_lustre" 1>&2
$(dirname $0)/eldarica_lustre.sh > $1_lustre_eldarica.csv 
echo "START hoice_lustre" 1>&2
$(dirname $0)/hoice_lustre.sh > $1_lustre_hoice.csv 
pkill -9 main 2> /dev/null
echo "START tb_ar_smt2_lustre" 1>&2
$(dirname $0)/tb_ar_smt2_lustre.sh > $1_lustre_tb_ar_smt.csv
pkill -9 main 2> /dev/null
echo "START tb_ar_smt2_lustre" 1>&2
$(dirname $0)/tb_smt2_lustre.sh > $1_lustre_tb_smt.csv
pkill -9 main 2> /dev/null
echo "START cvc4_su_lustre" 1>&2
$(dirname $0)/cvc4_su_lustre.sh > $1_lustre_cvc4_su.csv 