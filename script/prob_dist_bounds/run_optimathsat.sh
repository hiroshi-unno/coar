for file in $(ls ./benchmarks/QFL/distribution_bounds/*.qhes); do
    echo "";
    echo $file;
    time timeout 100 ./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_optimathsat_deg1.json -p qfl $file;
done
