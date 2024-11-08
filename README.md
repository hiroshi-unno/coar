# CoAR: Collection of Automated Reasoners

* RCaml: A refinement type checking and inference tool for OCaml and HFL
* EffCaml: A transformation-based verifier for effectful OCaml programs
* MuVal: A fixpoint logic validity checker based on pfwCSP solving
* MuCyc: A fixpoint logic validity checker based on cyclic-proof search
* PCSat: A CHC/pfwnCSP/SyGuS solver based on CEGIS
* OptPCSat: An optimizing CHC solver based on pfwnCSP solving

## Installation from source code

* Install opam2 (see [the official webpage](https://opam.ocaml.org/doc/Install.html)).
* Install ocaml-5.1.0:
  ```bash
  opam switch create 5.1.0
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
- `llvm2kittel` (https://github.com/gyggg/llvm2kittel/tree/kou)
- `ltl3ba` (https://sourceforge.net/projects/ltl3ba/)
- `horsat2` (https://github.com/hopv/horsat2)

## Installation with Docker

```bash
docker pull docker.io/library/ubuntu:22.04
docker pull docker.io/ocaml/opam:ubuntu-22.04-ocaml-5.2
sudo docker build -t coar .
```

## Usage

### Predicate Constraint Satisfiability Checking (CHC, $`\forall\exists`$CHC, pCSP, and pfwnCSP)

```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```
```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/AECHC/bar.smt2
```
```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/max.clp
```

### Syntax Guided Synthesis (INV and CLIA)

```bash
git submodule update --init benchmarks/sygus-comp/
dune exec main -- -c ./config/solver/dbg_pcsat_tbq_ar.json -p sygus ./benchmarks/sygus-comp/comp/2017/CLIA_Track/fg_max2.sl
```

### Regular Expression Synthesis

```bash
dune exec main -- -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/SyGuS/regex/ex1.smt2
```

### CHC Satisfiability Checking via Cyclic-Proof Search and Proof Refinement

#### `Ind(Ret(F, MBP(0)))` Configuration

```bash
dune exec main -- -c ./config/solver/mucyc_returnF_mbp0_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Ind(Yld(T, MBP(1)))` Configuration

```bash
dune exec main -- -c ./config/solver/mucyc_yieldTT_mbp1_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Ret(F, MBP(0))` Configuration

```bash
dune exec main -- -c ./config/solver/mucyc_returnF_mbp0.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Yld(T, MBP(1))` Configuration

```bash
dune exec main -- -c ./config/solver/mucyc_yieldTT_mbp1.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### `Solve` Configuration

```bash
dune exec main -- -c ./config/solver/mucyc.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

### Fixpoint Logic Validity Checking (muArith and $`\mu`$CLP)

#### Primal

```bash
dune exec main -- -c ./config/solver/dbg_muval_prove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Dual

```bash
dune exec main -- -c ./config/solver/dbg_muval_disprove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl2b-invalid.hes
```

#### Parallel

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Parallel with Clause Exchange

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### Interactive Conditional

```bash
dune exec main -- -c ./config/solver/muval_prove_nonopt_tbq_ar.json -p muclpinter ./benchmarks/muCLP/popl2023mod/sas2019_lines1.hes
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

### CHC Maximization

```bash
dune exec main -- -c ./config/solver/dbg_optpcsat_nc_tbq_ar.json -p chcmax ./benchmarks/CHC/popl2023opt/test2.smt2
```

### Verification of OCaml Programs via Refinement Type Inference using RCaml

#### Safety Verification
##### with PCSat

```bash
dune exec main -- -c ./config/solver/dbg_rcaml_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

##### with Spacer

```bash
dune exec main -- -c ./config/solver/dbg_rcaml_spacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

#### Temporal Verification (only for constraint generation)

```bash
dune exec main -- -c ./config/solver/dbg_rcaml_temp_eff_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/temporal/sum_term.ml
```

### Verification of OCaml Programs via Higher-Order Model Checking using EffCaml

Build `horsat2` and place it in the current directory.

```bash
dune exec main -- -c ./config/solver/dbg_effcaml.json -p ml ./benchmarks/OCaml/oopsla24/mutable_set_not_b_false_UNSAT.ml
```

### Verification of C Programs
#### LTL Verification

Build `ltl3ba` and place it in the current directory.

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cltl ./benchmarks/C/cav2015ltl/coolant/coolant_basis_1_safe_sfty.c
```

Please download and use the benchmark set of [Ultimate LTL Automizer](https://ultimate.informatik.uni-freiburg.de/downloads/ltlautomizer/).

#### CTL Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cctl ./benchmarks/C/pldi2013ctl/industrial/1-acqrel-AGimpAF-succeed.c
```

Please obtain and use the benchmark set from the following paper:
* Byron Cook and Eric Koskinen. Reasoning about nondeterminism in programs. PLDI 2013.

### Verification of Labeled Transition Systems
#### Termination Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsterm ./benchmarks/LTS/simple/test.t2
```

#### Non-Termination Verification

```bash
dune exec main -- -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsnterm ./benchmarks/LTS/simple/test.t2
```

#### Interactive Conditional (Non-)Termination Verification

```bash
dune exec main -- -c ./config/solver/muval_prove_tbq_ar.json -p ltsterminter ./benchmarks/LTS/simple/prog2.t2
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

## References

### RCaml

1. Taro Sekiyama and Hiroshi Unno. Algebraic Temporal Effects: Temporal Verification of Recursively Typed Higher-Order Programs. POPL 2025.

1. Satoshi Kura and Hiroshi Unno. Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System. ICFP 2024.

1. Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers. POPL 2024.

1. Taro Sekiyama and Hiroshi Unno. Temporal Verification with Answer-Effect Modification. POPL 2023.

1. Yoji Nanjo, Hiroshi Unno, Eric Koskinen, and Tachio Terauchi. A Fixpoint Logic and Dependent Effects for Temporal Property Verification. LICS 2018

1. Hiroshi Unno, Yuki Satake, and Tachio Terauchi. Relatively Complete Refinement Type System for Verification of Higher-Order Non-deterministic Programs. POPL 2018.

1. Kodai Hashimoto and Hiroshi Unno. Refinement Type Inference via Horn Constraint Optimization. SAS 2015.

1. Hiroshi Unno, Tachio Terauchi, and Naoki Kobayashi. Automating Relatively Complete Verification of Higher-Order Functional Programs. POPL 2013.

1. Hiroshi Unno and Naoki Kobayashi. Dependent Type Inference with Interpolants. PPDP 2009.

1. Hiroshi Unno and Naoki Kobayashi. On-Demand Refinement of Dependent Types. FLOPS 2008.

### EffCaml

1. Taro Sekiyama and Hiroshi Unno. Higher-Order Model Checking of Effect-Handling Programs with Answer-Type Modification. OOPSLA 2024.

### MuVal

1. Hiroshi Unno, Tachio Terauchi, Yu Gu, and Eric Koskinen. Modular Primal-Dual Fixpoint Logic Solving for Temporal Verification. POPL 2023.

1. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

### MuCyc

1. Takeshi Tsukada and Hiroshi Unno. Inductive Approach to Spacer. PLDI 2024.

1. Takeshi Tsukada and Hiroshi Unno. Software Model-Checking as Cyclic-Proof Search. POPL 2022.

1. Hiroshi Unno, Sho Torii, and Hiroki Sakamoto. Automating Induction for Solving Horn Clauses. CAV 2017.

### PCSat

1. Minchao Wu, Takeshi Tsukada, Hiroshi Unno, Taro Sekiyama, and Kohei Suenaga. Learning Heuristics for Template-based CEGIS of Loop Invariants with Reinforcement Learning.

1. Yu Gu, Takeshi Tsukada, and Hiroshi Unno. Optimal CHC Solving via Termination Proofs. POPL 2023.

1. Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021.

1. Yuki Satake, Hiroshi Unno, and Hinata Yanagi. Probabilistic Inference for Predicate Constraint Satisfaction. AAAI 2020.

## Acknowledgements

We thank Hiroyuki Katsura and Philippe Heim for reporting bugs in PCSat and MuVal, respectively. We are also grateful to the organizer of termCOMP 2023, Akihisa Yamada, and participants Florian Frohn and Nils Lommen, as thanks to them, we were able to identify a bug in MuVal.
