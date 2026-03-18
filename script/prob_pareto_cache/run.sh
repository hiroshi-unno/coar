for file in $(ls ./benchmarks/QFL/pareto_caching/*.qhes); do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/muval_quant_pc_polyqent_deg1.json -p qfl $file;
done
