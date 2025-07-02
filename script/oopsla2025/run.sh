for file in $(ls ./benchmarks/OCaml/oopsla25/*.ml); do
    echo "";
    echo $file;
    time ./_build/default/main.exe -c ./config/solver/effcaml.json -p ml $file;
done