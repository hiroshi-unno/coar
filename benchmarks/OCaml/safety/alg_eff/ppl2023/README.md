# Benchmarks for "Refinement Type System for Algebraic Effects and Handlers"

## How To Run

1. Install CoAR (this repository) following [the installation guide](https://github.com/hiroshi-unno/coar/blob/main/README.md).

2. Run the following command.
    ```bash
    dune exec main -- -c ./config/solver/rcaml_pcsat_adt_inv_tb_ar.json -p ml ./benchmarks/OCaml/safety/alg_eff/ppl2023/<filename>.ml
    ```

## Example
```bash
$ dune exec main -- -c ./config/solver/rcaml_pcsat_adt_inv_tb_ar.json -p ml ./benchmarks/OCaml/safety/alg_eff/ppl2023/decide-max.ml
...
sat,11         @assert type_of(main) <: ($x911:unit) -> {$v915: int | $v915:i = 19} [#1]
```