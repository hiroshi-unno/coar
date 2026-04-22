# CoAR: Collection of Automated Reasoners

* RCaml: A refinement type checking and inference tool for OCaml
* EffCaml: A software model checker for effectful OCaml programs
* [Thrust: A refinement type checking and inference tool for Rust](https://github.com/coord-e/thrust)
* Athena: A software model checker for C
* MuVal: A fixpoint logic validity checker based on predicate constraint solving
* MuCyc: A fixpoint logic validity checker based on cyclic-proof search and proof refinement
* MuStrat: A fixpoint logic validity checker based on strategy synthesis
* PCSat: A predicate constraint solver based on CEGIS
* OptPCSat: An optimizing CHC solver based on predicate constraint solving
* HOMCSat: A SAT/QSAT/DQSAT/HOSAT solver based on higher-order model checking

An overview of the fixed-point logic solvers MuVal, MuStrat, and MuCyc for $`\mu`$CLP, HFL, QFL, and QHFL, along with the backend solver PCSat used in MuVal, is provided in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/epit2025.pdf). An overview of the verification methods for algebraic effects and handlers implemented in RCaml and EffCaml is available in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/chocola2025.pdf), and a summary of techniques for relational verification using PCSat and MuCyc can be found in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/vmcai2024.pdf).


## Installation from source code

* Install opam2 (see [the official webpage](https://opam.ocaml.org/doc/Install.html)).
* Install ocaml-5.4.0:
  ```bash
  opam switch create 5.4.0
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
* Run:
  ```bash
  ./_build/default/main.exe -c <config_file> -p <problem_type> <target_file>
  ```
* Build & Run:
  ```bash
  dune exec main -- -c <config_file> -p <problem_type> <target_file>
  ```
* Document generation (to `_build/default/_doc/_html`):
  ```bash
  opam install odoc
  dune build @doc
  ```

### Required OCaml packages:

* `core`
* `core_unix`
* `domainslib`
* `menhir`
* `ppx_deriving_yojson`
* `ocaml-compiler-libs`
* `ocamlgraph`
* `zarith`
* `z3`
* `minisat`
* `libsvm` with some modification (https://github.com/hiroshi-unno/libsvm-ocaml.git)
* `camlzip`

### External tools (optional):

- `hoice` (https://github.com/hopv/hoice)
- `clang` (https://clang.llvm.org/)
- `llvm2kittel` (https://github.com/addmai/llvm2kittel/tree/termcomp2025)
- `ltl3ba` (https://sourceforge.net/projects/ltl3ba/)
- `horsat2` (https://github.com/hopv/horsat2)
- `polyqent` (https://github.com/ChatterjeeGroup-ISTA/polyqent)
- `optimathsat` (https://optimathsat.disi.unitn.it/)

## Installation with Docker

```bash
docker pull ghcr.io/hiroshi-unno/coar:main
```

or

```bash
sudo docker build -t coar .
```

## Usage

### Verification of OCaml Programs via Refinement Type Inference using RCaml

#### Safety Verification
##### with PCSat

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

##### with GSpacer

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_gspacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

##### with Spacer

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_spacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

#### Temporal Verification (only for constraint generation)

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_temp_eff_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/temporal/sum_term.ml
```

### Verification of OCaml Programs via Higher-Order Model Checking using EffCaml

Build `horsat2` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_effcaml.json -p ml ./benchmarks/OCaml/oopsla24/mutable_set_not_b_false_UNSAT.ml
```

### Verification of C Programs via Fixpoint Logic Validity Checking using MuVal
#### LTL Verification

Build `ltl3ba` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cltl ./benchmarks/C/cav2015ltl/coolant/coolant_basis_1_safe_sfty.c
```

Please download and use the benchmark set of [Ultimate LTL Automizer](https://ultimate.informatik.uni-freiburg.de/downloads/ltlautomizer/).

#### CTL Verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cctl ./benchmarks/C/pldi2013ctl/industrial/1-acqrel-AGimpAF-succeed.c
```

Please obtain and use the benchmark set from the following paper:
* Byron Cook and Eric Koskinen. Reasoning about nondeterminism in programs. PLDI 2013.

### Verification of Labeled Transition Systems via Fixpoint Logic Validity Checking using MuVal
#### Termination Verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsterm ./benchmarks/LTS/simple/test.t2
```

#### Non-Termination Verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsnterm ./benchmarks/LTS/simple/test.t2
```

#### Interactive Conditional (Non-)Termination Verification

```bash
./_build/default/main.exe -c ./config/solver/muval_prove_tbq_ar.json -p ltsterminter ./benchmarks/LTS/simple/prog2.t2
```

The following interaction example demonstrates conditional termination analysis, which proves that the program [prog2.c](benchmarks/LTS/simple/prog2.c) terminates when the initial value of the variable `x` is 9 or less, and diverges otherwise.

```
timeout in sec: 10
action (primal/dual/unknown/pos/neg/end): primal
v0 <= 8 /\ v0 >= 2
action (primal/dual/unknown/pos/neg/end): primal
1 > v0 \/ v0 <= 8 /\ v0 >= 2
action (primal/dual/unknown/pos/neg/end): primal
v0 <= 9 /\ v0 > 8 \/ 1 > v0 \/ v0 <= 8 /\ v0 >= 2
action (primal/dual/unknown/pos/neg/end): dual
v0 mod 2 != 0 /\ v0 >= 10
action (primal/dual/unknown/pos/neg/end): dual
v0 >= 10
action (primal/dual/unknown/pos/neg/end): primal
v0 <= 9
maximality is guaranteed
```

Here, the `primal` (resp. `dual`) action lets MuVal infer a precondition under which the program terminates (resp. diverges), but note that MuVal does not necessarily return the *weakest* precondition. By repeating sets of `primal` and `dual` actions, it is finally proved that the program terminates if and only if the initial value of the variable `x` is 9 or less.

### Predicate Constraint Satisfiability Checking (CHC, $`\forall\exists`$CHC, pCSP, and pfwnCSP) using PCSat

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```
```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/AECHC/bar.smt2
```
```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/max.clp
```

### Syntax Guided Synthesis (INV and CLIA) using PCSat

```bash
git submodule update --init benchmarks/sygus-comp/
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p sygus ./benchmarks/sygus-comp/comp/2017/CLIA_Track/fg_max2.sl
```

### Regular Expression Synthesis using PCSat

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/SyGuS/regex/ex1.smt2
```

### CHC Maximization using OptPCSat

```bash
./_build/default/main.exe -c ./config/solver/dbg_optpcsat_nc_tbq_ar.json -p chcmax ./benchmarks/CHC/popl2023opt/test2.smt2
```

### CHC Satisfiability Checking using MuCyc

#### `Ind(Ret(F, MBP(0)))` Configuration

```bash
./_build/default/main.exe -c ./config/solver/mucyc_returnF_mbp0_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Ind(Yld(T, MBP(1)))` Configuration

```bash
./_build/default/main.exe -c ./config/solver/mucyc_yieldTT_mbp1_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Ret(F, MBP(0))` Configuration

```bash
./_build/default/main.exe -c ./config/solver/mucyc_returnF_mbp0.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Yld(T, MBP(1))` Configuration

```bash
./_build/default/main.exe -c ./config/solver/mucyc_yieldTT_mbp1.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Solve` Configuration

```bash
./_build/default/main.exe -c ./config/solver/mucyc.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

### Fixpoint Logic Validity Checking (muArith and $`\mu`$CLP)

#### with MuVal (Primal Mode)

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_prove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### with MuVal (Dual Mode)

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_disprove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl2b-invalid.hes
```

#### with MuVal (Parallel Mode)

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### with MuVal (Parallel Mode with Clause Exchange)

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### with MuVal (Interactive Conditional Mode)

```bash
./_build/default/main.exe -c ./config/solver/muval_prove_nonopt_tbq_ar.json -p muclpinter ./benchmarks/muCLP/popl2023mod/sas2019_lines1.hes
```

The following is an example of using MuVal to interactively prove that there is no input that satisfies the given $`\mu`$CLP query.

```
timeout in sec: 10
action (primal/dual/unknown/pos/neg/end): dual
m mod 2 = 0 /\ m <= 0 /\ m - n >= 0 /\ 1 > m - n
action (primal/dual/unknown/pos/neg/end): pos
positive examples: m > 0
action (primal/dual/unknown/pos/neg/end): dual
m >= 1 \/ m mod 2 = 0 /\ m - n >= 0 /\ 1 > m - n
action (primal/dual/unknown/pos/neg/end): unknown
1 > m /\ (0 > m - n \/ m mod 2 != 0 \/ 1 <= m - n)
action (primal/dual/unknown/pos/neg/end): pos
positive examples: 1 > m /\ 1 <= m - n
action (primal/dual/unknown/pos/neg/end): dual
m >= 1 \/ 0 > n - m \/ m mod 2 = 0 /\ m - n >= 0
action (primal/dual/unknown/pos/neg/end): unknown
0 <= n - m /\ 1 > m /\ (m mod 2 != 0 \/ 0 > m - n)
action (primal/dual/unknown/pos/neg/end): pos
positive examples: 0 <= n - m /\ 1 > m /\ m mod 2 != 0
action (primal/dual/unknown/pos/neg/end): dual
m - n >= 0 \/ m mod 2 != 0 \/ m >= 1
action (primal/dual/unknown/pos/neg/end): unknown
m mod 2 = 0 /\ 0 > m - n /\ 1 > m
action (primal/dual/unknown/pos/neg/end): pos
positive examples: m mod 2 = 0 /\ 0 > m - n /\ 1 > m
action (primal/dual/unknown/pos/neg/end): dual
true
maximality is guaranteed
```

Here, the `dual` action lets MuVal infer a precondition under which the query does not hold, but note that MuVal does not necessarily return the *weakest* precondition. Before performing the `dual` action, hints about an input range that should be included in the weakest precondition are provided through the `pos` action. By repeating sets of `pos` and `dual` actions, it is finally proved that there is no input that satisfies the given $`\mu`$CLP query.

### QFL Validity Checking using MuVal<sup>QFL</sup>

Build `PolyQEnt` and place it to run as `./polyqent/PolyQEnt`.
```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_quant_polyqent_deg3.json -p qfl ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
```

### HFL and QHFL Validity Checking using MuVal<sup>HFL</sup> and MuVal<sup>QHFL</sup>

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/quantitative/icfp24/coin_flip_unif.ml
```

### Quantified SMT Solving

#### with MuCyc

```bash
./_build/default/main.exe -c ./config/solver/mucyc.json -p smt ./benchmarks/QSMT/max.smt2
```

### Boolean Satisfiability Checking (SAT, QSAT, DQSAT, and HOSAT) using HOMCSat

Build `horsat2` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p sat ./benchmarks/SAT/easy2.dimacs
```
```bash
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p dqsat ./benchmarks/QSAT/test.qdimacs
```
```bash
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p dqsat ./benchmarks/QSAT/test.dqdimacs
```
```bash
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p hosat ./benchmarks/HOSAT/AAAI2025/cps-arity1_ord3.hosat
```

## References

### RCaml

1. Satoshi Kura, Marco Gaboardi, Taro Sekiyama, and Hiroshi Unno. A Category-Theoretic Framework for Dependent Effect Systems. ESOP 2026.

1. Taro Sekiyama and Hiroshi Unno. Algebraic Temporal Effects: Temporal Verification of Recursively Typed Higher-Order Programs. POPL 2025.

1. Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers. POPL 2024.

1. Taro Sekiyama and Hiroshi Unno. Temporal Verification with Answer-Effect Modification. POPL 2023.

1. Yoji Nanjo, Hiroshi Unno, Eric Koskinen, and Tachio Terauchi. A Fixpoint Logic and Dependent Effects for Temporal Property Verification. LICS 2018

1. Hiroshi Unno, Yuki Satake, and Tachio Terauchi. Relatively Complete Refinement Type System for Verification of Higher-Order Non-deterministic Programs. POPL 2018.

1. Kodai Hashimoto and Hiroshi Unno. Refinement Type Inference via Horn Constraint Optimization. SAS 2015.

1. Hiroshi Unno, Tachio Terauchi, and Naoki Kobayashi. Automating Relatively Complete Verification of Higher-Order Functional Programs. POPL 2013.

1. Hiroshi Unno and Naoki Kobayashi. Dependent Type Inference with Interpolants. PPDP 2009.

1. Hiroshi Unno and Naoki Kobayashi. On-Demand Refinement of Dependent Types. FLOPS 2008.

### EffCaml

1. Taro Sekiyama, Ugo Dal Lago, and Hiroshi Unno. On Higher-Order Model Checking of Effectful Answer-Type-Polymorphic Programs. OOPSLA 2025.

1. Taro Sekiyama and Hiroshi Unno. Higher-Order Model Checking of Effect-Handling Programs with Answer-Type Modification. OOPSLA 2024.

### Thrust

1. Hiromi Ogawa, Taro Sekiyama, and Hiroshi Unno. Thrust: A Prophecy-based Refinement Type System for Rust. PLDI 2025.

### Athena

1. Negar Fathi, Hiroshi Unno, Tachio Terauchi, and Rahul Purandare. Sound Termination and Non-Termination Analysis of C Programs with Bit-Precise Bounded Semantics and Advanced Constructs. FSE 2026.

### PCSat & OptPCSat

1. Yu Gu, Takeshi Tsukada, and Hiroshi Unno. Optimal CHC Solving via Termination Proofs. POPL 2023.

1. Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

1. Yuki Satake, Hiroshi Unno, and Hinata Yanagi. Probabilistic Inference for Predicate Constraint Satisfaction. AAAI 2020.

### MuVal & MuVal<sup>HFL</sup> & MuVal<sup>QFL</sup> & MuVal<sup>QHFL</sup>

1. Kazuki Watanabe, Mayuko Kori, Taro Sekiyama, Satoshi Kura, and Hiroshi Unno. A Categorical Product Construction for Temporal Verification of Effectful Higher-Order Programs. 2026.

1. Satoshi Kura and Hiroshi Unno. A Hierarchy of Supermartingales for &omega;-Regular Verification. PLDI 2026.

1. Satoshi Kura, Hiroshi Unno, and Takeshi Tsukada. Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification. PLDI 2026.

1. Satoshi Kura and Hiroshi Unno. Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System. ICFP 2024.

1. Hiroshi Unno, Tachio Terauchi, Yu Gu, and Eric Koskinen. Modular Primal-Dual Fixpoint Logic Solving for Temporal Verification. POPL 2023.

1. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

### MuCyc

1. Ivana Bocevska, Takeshi Tsukada, Hiroshi Unno, Oded Padon, and Sharon Shoham. Lagrangian-Based Duality for Quantified SMT Algorithms. CAV 2026.

1. Takeshi Tsukada and Hiroshi Unno. Inductive Approach to Spacer. PLDI 2024.

1. Takeshi Tsukada and Hiroshi Unno. Software Model-Checking as Cyclic-Proof Search. POPL 2022.

1. Hiroshi Unno, Sho Torii, and Hiroki Sakamoto. Automating Induction for Solving Horn Clauses. CAV 2017.

### MuStrat

1. Takeshi Tsukada, Hiroshi Unno, Oded Padon, and Sharon Shoham. A Primal-Dual Perspective on Program Verification Algorithms. POPL 2025.

### HOMCSat

1. Hiroshi Unno, Takeshi Tsukada, and Jie-Hong Roland Jiang. Solving Higher-Order Quantified Boolean Satisfiability via Higher-Order Model Checking. AAAI 2025.

## Acknowledgements

We thank Ziteng Wang for contributing the Docker build workflow. We also thank Hiroyuki Katsura, Philippe Heim, Ehsan Goharshady, Elaine Li, Benedikt Maderbacher, and Alvin George for reporting bugs in PCSat and MuVal. We are also grateful to the organizer of termCOMP 2023, Akihisa Yamada, and participants Florian Frohn and Nils Lommen, as thanks to them, we were able to identify a bug in MuVal. We further thank Florian Frohn, as the organizer of termCOMP 2025, for valuable feedback that helped improve the robustness of MuVal’s C program (non-)termination verification. We also thank the artifact evaluation committees of POPL, PLDI, CAV, OOPSLA, and ICFP for their valuable feedback.
