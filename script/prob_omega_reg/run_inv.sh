pldi26_benchmarks=(
    "./benchmarks/QFL/omega_regular_invariant/ex3_8.qhes"
    "./benchmarks/QFL/omega_regular_invariant/ex4_11.qhes"
    "./benchmarks/QFL/omega_regular_invariant/ex3_9.qhes"
    "./benchmarks/QFL/omega_regular_invariant/ex3_9_rw.qhes"
    "./benchmarks/QFL/omega_regular_invariant/null_recurrence.qhes"
    "./benchmarks/QFL/omega_regular_invariant/EvenOrNegative.qhes"
    "./benchmarks/QFL/omega_regular_invariant/PersistRW.qhes"
    "./benchmarks/QFL/omega_regular_invariant/RecurRW.qhes"
    "./benchmarks/QFL/omega_regular_invariant/GuaranteeRW.qhes"
    "./benchmarks/QFL/omega_regular_invariant/SafeRWalk1.qhes"
    "./benchmarks/QFL/omega_regular_invariant/SafeRWalk2.qhes"
    "./benchmarks/QFL/omega_regular_invariant/Temperature1.qhes"
    "./benchmarks/QFL/omega_regular_invariant/Temperature2.qhes"
    "./benchmarks/QFL/omega_regular_invariant/Temperature3.qhes"
    "./benchmarks/QFL/omega_regular_invariant/Temperature4.qhes"
    "./benchmarks/QFL/omega_regular_invariant/FinMemoryControl.qhes"
)

echo
echo "=============== LexPMSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_lexpmsm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== LexGSSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_lexgssm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== PMSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_pmsm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== GSSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_gssm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== SSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_ssm_polyqent_deg1.json -p qfl $file;
done
