# CoAR: Collection of Automated Reasoners

* MuVal: A fixpoint logic validity checker based on pfwCSP solving
* PCSat: A pfwCSP solver based on CEGIS

## Installation

Install opam2, ocaml, and dune.

* install required packages: `opam install . --deps-only`
  (You may also need to install `libblas-dev`, `liblapack-dev`, `libmpfr-dev`, `libgmp-dev`, `libffi-dev`, and `pkg-config`)
* build: `dune build main.exe`
* build & run: `dune exec main -- -c <config_file> -p <problem_type> <target_file>`
* document generation: `dune build @doc` (for `_build/default/_doc/_html`)

Required OCaml packages:

* `zarith`
* `z3`
* `core`
* `minisat`
* `menhir`
* `yojson`
* `ppx_deriving_yojson`
* `async`
* `ocamlgraph`
* `libsvm` with some modification (https://github.com/umedaikiti/libsvm-ocaml.git)

## Usage of PCSat

### CHC/pCSP/pfwCSP Satisfiability Checking
`dune exec main -- -c ./config/solver/dbg_pcsat_tb_ucore.json -p pcsp benchmarks/chc-test/sum.smt2`

## Usage of MuVal

### Termination Verification of Labeled Transition Systems
`dune exec main -- -c ./config/solver/dbg_muval_tb_ucore_prove.json -p ltsterm benchmarks/lts-term-test/test.t2`

### Interactive Conditional (Non-)Termination Verification of Labeled Transition Systems
`dune exec main -- -c ./config/solver/muval_tb_ucore_prove.json -p ltscterm benchmarks/lts-cterm-test/prog2.t2`

## References

1. Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

2. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

3. Yuki Satake, Hiroshi Unno, and Hinata Yanagi. Probabilistic Inference for Predicate Constraint Satisfaction. AAAI 2020.