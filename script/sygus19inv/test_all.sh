echo "START tb_ar_sygus19inv" 1>&2
$(dirname $0)/tb_ar.sh > $1_sygus19inv_tb_ar.csv
pkill -9 main 2> /dev/null
echo "START tb_sygus19inv" 1>&2
$(dirname $0)/tb.sh > $1_sygus19inv_tb.csv
pkill -9 main 2> /dev/null
echo "START spacer_sygus19inv" 1>&2
$(dirname $0)/spacer.sh > $1_sygus19inv_spacer.csv
pkill -9 main 2> /dev/null
echo "START eldarica_sygus19inv" 1>&2
$(dirname $0)/eldarica.sh > $1_sygus19inv_eldarica.csv 
echo "START hoice_sygus19inv" 1>&2
$(dirname $0)/hoice.sh > $1_sygus19inv_hoice.csv 
