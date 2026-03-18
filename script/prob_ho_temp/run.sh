for file in $(ls ./benchmarks/OCaml/quantitative/temporal_safety/*.ml); do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/rcaml_pcsat_tbq_ar.json -p ml $file;
done

for file in $(ls ./benchmarks/OCaml/quantitative/partial_expected_reward/*.ml); do
    echo "";
    echo $file;
    time timeout 180 ./_build/default/main.exe -c ./config/solver/rcaml_pcsat_tbq_ar.json -p ml $file;
done
