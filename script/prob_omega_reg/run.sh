pldi26_benchmarks=(
    "./benchmarks/QFL/omega_regular/ex3_8.qhes"
    "./benchmarks/QFL/omega_regular/ex4_11.qhes"
    "./benchmarks/QFL/omega_regular/ex3_9.qhes"
    "./benchmarks/QFL/omega_regular/ex3_9_rw.qhes"
    # "./benchmarks/QFL/omega_regular/null_recurrence.qhes"
    "./benchmarks/QFL/omega_regular/EvenOrNegative.qhes"
    "./benchmarks/QFL/omega_regular/PersistRW.qhes"
    "./benchmarks/QFL/omega_regular/RecurRW.qhes"
    "./benchmarks/QFL/omega_regular/GuaranteeRW.qhes"
    # "./benchmarks/QFL/omega_regular/SafeRWalk1.qhes"
    # "./benchmarks/QFL/omega_regular/SafeRWalk2.qhes"
    # "./benchmarks/QFL/omega_regular/Temperature1.qhes"
    "./benchmarks/QFL/omega_regular/Temperature2.qhes"
    # "./benchmarks/QFL/omega_regular/Temperature3.qhes"
    # "./benchmarks/QFL/omega_regular/Temperature4.qhes"
    # "./benchmarks/QFL/omega_regular/FinMemoryControl.qhes"
)


# Progress: each run's position among all of them and the time since the script began.
total=$(( ${#pldi26_benchmarks[@]} * 5 ))
i=0
SECONDS=0
elapsed() { printf '%02d:%02d:%02d' $((SECONDS / 3600)) $((SECONDS % 3600 / 60)) $((SECONDS % 60)); }

echo
echo "=============== LexPMSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    i=$((i + 1)); echo "[$i/$total] $file (elapsed $(elapsed))";
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_lexpmsm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== LexGSSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    i=$((i + 1)); echo "[$i/$total] $file (elapsed $(elapsed))";
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_lexgssm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== PMSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    i=$((i + 1)); echo "[$i/$total] $file (elapsed $(elapsed))";
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_pmsm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== GSSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    i=$((i + 1)); echo "[$i/$total] $file (elapsed $(elapsed))";
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_gssm_polyqent_deg1.json -p qfl $file;
done

echo
echo "=============== SSM ===============";
for file in "${pldi26_benchmarks[@]}"; do
    echo "";
    i=$((i + 1)); echo "[$i/$total] $file (elapsed $(elapsed))";
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_omega_ssm_polyqent_deg1.json -p qfl $file;
done
