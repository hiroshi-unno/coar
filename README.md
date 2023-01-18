# CoAR: Collection of Automated Reasoners

* RCaml: A refinement type checking and inference tool for OCaml
* MuVal: A fixpoint logic validity checker based on pfwCSP solving
* PCSat: A CHC/pfwnCSP/SyGuS solver based on CEGIS
* OptPCSat: An optimizing CHC solver based on pfwnCSP solving

## Installation from source code

* Install opam2.
* Install ocaml-5.0.0:
  ```bash
  opam switch create 5.0.0
  ```
* Install dune:
  ```bash
  opam install dune
  ```
* Install required packages:
  ```bash
  opam install . --deps-only
  ```
  (You may also need to install `libblas-dev`, `liblapack-dev`, `libmpfr-dev`, `libgmp-dev`, `libglpk-dev`, `libffi-dev`, and `pkg-config`)
* Build:
  ```bash
  dune build main.exe
  ```
* Build & Run:
  ```bash
  dune exec main -- -c <config_file> -p <problem_type> <target_file>
  ```
* Document generation (to `_build/default/_doc/_html`):
  ```bash
  dune build @doc
  ```

### Required OCaml packages:

* `core`
* `core_unix`
* `menhir`
* `ppx_deriving_yojson`
* `ocaml-compiler-libs`
* `ocamlgraph`
* `zarith`
* `z3`
* `minisat`
* `libsvm` with some modification (https://github.com/hiroshi-unno/libsvm-ocaml.git)
* `domainslib`

### External tools (optional):

- `hoice` (https://github.com/hopv/hoice)
- `clang` (https://clang.llvm.org/)
- `llvm2kittel` (https://github.com/gyggg/llvm2kittel)
- `ltl3ba` (https://sourceforge.net/projects/ltl3ba/)

## Installation with Docker

```bash
docker pull docker.io/library/ubuntu:22.04
docker pull docker.io/ocaml/opam:ubuntu-22.04-ocaml-5.0
sudo docker build -t coar .
```

## Usage

### Predicate Constraint Satisfiability Checking (CHC, $\forall\exists$ CHC, pCSP, and pfwnCSP)

```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tb_ar.json -p pcsp benchmarks/CHC/simple/sum.smt2
```
```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tb_ar.json -p pcsp benchmarks/AECHC/bar.smt2
```
```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tb_ar.json -p pcsp benchmarks/pfwnCSP/simple/max.clp
```

### Syntax Guided Synthesis (INV and CLIA)

```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tb_ar.json -p sygus ./benchmarks/sygus-comp/comp/2017/CLIA_Track/fg_max2.sl
```

### Fixpoint Logic Validity Checking (muArith and muCLP)

#### Primal

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tb_ar.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Dual

```bash
dune exec main -- -c ./config/solver/dbg_muval_disprove_tb_ar.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Parallel

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_tb_ar.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Parallel with Clause Exchange

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tb_ar.json -p muclp benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

### Verification of OCaml Programs

#### with PCSat

```bash
dune exec main -- -c ./config/solver/dbg_rcaml_pcsat_tb_ar.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

#### with Spacer

```bash
dune exec main -- -c ./config/solver/dbg_rcaml_spacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

### Verification of C Programs
#### LTL Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tb_ar.json -p cltl <file>
```

#### CTL Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tb_ar.json -p cctl <file>
```

### Verification of Labeled Transition Systems
#### Termination Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tb_ar.json -p ltsterm benchmarks/LTS/simple/test.t2
```

#### Non-Termination Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tb_ar.json -p ltsnterm benchmarks/LTS/simple/test.t2
```

#### Interactive Conditional (Non-)Termination Verification

```bash
dune exec main -- -c ./config/solver/muval_prove_tb_ar.json -p ltscterm benchmarks/LTS/simple/prog2.t2
```

## References

### RCaml

1. Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers.

1. Taro Sekiyama and Hiroshi Unno. Temporal Verification with Answer-Effect Modification. POPL 2023.

1. Yoji Nanjo, Hiroshi Unno, Eric Koskinen, and Tachio Terauchi. A Fixpoint Logic and Dependent Effects for Temporal Property Verification. LICS 2018

1. Hiroshi Unno, Yuki Satake, and Tachio Terauchi. Relatively Complete Refinement Type System for Verification of Higher-Order Non-deterministic Programs. POPL 2018.

1. Kodai Hashimoto and Hiroshi Unno. Refinement Type Inference via Horn Constraint Optimization. SAS 2015.

1. Hiroshi Unno, Tachio Terauchi, and Naoki Kobayashi. Automating Relatively Complete Verification of Higher-Order Functional Programs. POPL 2013.

1. Hiroshi Unno and Naoki Kobayashi. Dependent Type Inference with Interpolants. PPDP 2009.

1. Hiroshi Unno and Naoki Kobayashi. On-Demand Refinement of Dependent Types. FLOPS 2008.

### MuVal

1. Hiroshi Unno, Tachio Terauchi, Yu Gu, and Eric Koskinen. Modular Primal-Dual Fixpoint Logic Solving for Temporal Verification. POPL 2023.

1. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

### PCSat

1. Minchao Wu, Takeshi Tsukada, Hiroshi Unno, Taro Sekiyama, and Kohei Suenaga. Learning Heuristics for Template-based CEGIS of Loop Invariants with Reinforcement Learning.

1. Yu Gu, Takeshi Tsukada, and Hiroshi Unno. Optimal CHC Solving via Termination Proofs. POPL 2023.

1. Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

1. Yuki Satake, Hiroshi Unno, and Hinata Yanagi. Probabilistic Inference for Predicate Constraint Satisfaction. AAAI 2020.
