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

An overview of the fixed-point logic solvers MuVal, MuStrat, and MuCyc for $`\mu`$CLP, HFL, QFL, and QHFL, along with the backend solver PCSat used in MuVal, is provided in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/epit2025.pdf). An overview of the verification methods for algebraic effects and handlers implemented in RCaml and EffCaml is available in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/chocola2025.pdf), and a summary of techniques for relational verification using PCSat and MuCyc can be found in [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/vmcai2024.pdf). For a summary of some of the satisfiability and validity-checking problem classes supported by CoAR, please refer to [these slides](https://www.riec.tohoku.ac.jp/~unno/slides/ismvl2026.pdf).

## Contents

* [Installation](#installation)
* [Usage](#usage): running the tool, [which invocation do I want?](#which-invocation-do-i-want), reading the answer, configuration
* [Program verification](#program-verification): OCaml and C programs, probabilistic programs (pGCL and SGCL)
* [Transition system verification](#transition-system-verification): labeled transition systems (T2), integer transition systems of the Termination Competition, BTOR2 hardware models
* [Constraint solving](#constraint-solving): CHC and its extensions, CHC maximization, SyGuS, regular expressions
* [Fixpoint logic](#fixpoint-logic): muArith and muCLP, QFL, HFL and QHFL
* [SMT](#smt): quantified SMT
* [Higher-order model checking and Boolean satisfiability](#higher-order-model-checking-and-boolean-satisfiability)
* [Printing a problem instead of solving it](#printing-a-problem-instead-of-solving-it)
* [Artifacts](#artifacts), [References](#references), [Acknowledgements](#acknowledgements)

## Installation

### From source code

* Install opam2 (see [the official webpage](https://opam.ocaml.org/doc/Install.html)).
* Install ocaml-5.4.0:
  ```bash
  opam switch create 5.4.0
  ```
* Install the required packages, including dune (>= 3.10) (you may also need to install
  `libblas-dev`, `liblapack-dev`, `libmpfr-dev`, `libgmp-dev`, `libglpk-dev`, `libffi-dev`, and
  `pkg-config`):
  ```bash
  opam install . --deps-only
  ```
* Build:
  ```bash
  dune build main.exe
  ```
* Run:
  ```bash
  ./_build/default/main.exe -c <config_file> -p <problem_type> <target_file>
  ```
* Build and run in one step (slower than running the binary: see [Running the tool](#running-the-tool)):
  ```bash
  dune exec main -- -c <config_file> -p <problem_type> <target_file>
  ```
* Generate the documentation (to `_build/default/_doc/_html`):
  ```bash
  opam install odoc
  dune build @doc
  ```

### Required OCaml packages

* `dune` (>= 3.10)
* `core`
* `core_unix`
* `domainslib`
* `menhir`
* `ppx_deriving_yojson`
* `ocaml-compiler-libs`
* `ocamlgraph`
* `zarith`
* `z3` 5.1.0 or later (the version the tool is tested with; earlier versions answer some array
  questions wrongly). Building the `z3` package needs a C++ compiler with `<format>`, for example
  GCC 13 or later (`CC=gcc-13 CXX=g++-13 opam install z3` where the system compiler is older).
* `minisat`
* `libsvm` with some modification (https://github.com/hiroshi-unno/libsvm-ocaml.git)
* `camlzip`
* `apronext`

### External tools (optional)

Each is needed only by the backends or scripts named beside it. Paths are relative to the
repository root, from which the tool is run.

| tool | used by | where it is looked for | source |
| --- | --- | --- | --- |
| `hoice` | the HoIce backend for CHC (`hoice.json`) | `./hoice`, else `PATH` | https://github.com/hopv/hoice |
| `horsat2` | higher-order model checking with HorSat2 (`horsat2.json`) | `./horsat2` | https://github.com/hopv/horsat2 |
| `trecs` | higher-order model checking with TRecS (`trecs.json`) | `./trecs` | |
| `ltl3ba` | LTL verification of C programs (`-p cltl`) | `./ltl3ba`, else `PATH` | https://sourceforge.net/projects/ltl3ba/ |
| `polyqent` | the QFL backend PolyQEnt | `./polyqent/PolyQEnt` (the `path` field of its config) | https://github.com/ChatterjeeGroup-ISTA/polyqent |
| `optimathsat` | bounds on posterior distributions in QFL, when enabled in the config | `./optimathsat.exe` | https://optimathsat.disi.unitn.it/ |
| `cvc5` | a second opinion only: the `check_solution` certificate check (off by default) runs on Z3 and asks cvc5 again about a constraint Z3 left undecided, and a few optional PCSat proof steps (off by default) ask it; without cvc5 such a constraint is reported unchecked, never failed | `./cvc5`, else `PATH` | https://cvc5.github.io/ |
| `clang`, `llvm2kittel` | scripts that translate C programs to T2 transition systems | as set in each script | https://clang.llvm.org/, https://github.com/addmai/llvm2kittel/tree/svcomp2026 |

### With Docker

```bash
docker pull ghcr.io/hiroshi-unno/coar:main
```

or

```bash
sudo docker build -t coar .
```

The Dockerfile packages the CoAR executable, configurations, OCaml runtime library and Z3/Apron shared libraries. External backends such as Hoice, PolyQEnt, TRecS, HorSat2, OptiMathSAT and the standalone Z3 executable require separate installation. cvc5 is also omitted by default; add `--build-arg WITH_CVC5=1` to install its static release binary (version `CVC5_VERSION`, default 1.4.1) into `/root/coar`, which is on `PATH`.

The container starts in `/root/coar`, where relative configuration paths resolve. After the local build above, start an interactive shell with your inputs mounted:

```bash
docker run --rm -it -v "$PWD/benchmarks:/inputs:ro" coar
```

Inside that shell, run `main.exe -c config/solver/<config>.json -p <problem> /inputs/<input>`. Select an in-process backend unless you installed its external tools.

## Usage

### Running the tool

Every invocation has the same shape:

```bash
./_build/default/main.exe -c <config.json> -p <problem> <input>
```

`dune exec main -- -c <config.json> -p <problem> <input>` runs the same program, but every call first
has dune bring the build up to date (rebuilding whatever changed since the last build). Even with
nothing to rebuild that check takes seconds (about 5 s here, against 0.1 s for the binary to start),
so run the binary when running many inputs.

**Run it from the repository root.** Configurations reference other configurations by relative
path, and some backends look for external tools in the working directory (see
[External tools](#external-tools-optional)), so a run started elsewhere fails even when `-c` is
given as an absolute path. Temporary files
(`temp_*.smt2`, `output_graph_*.dot`) are written to the working directory for the same reason.

`-c` and `-p` must be compatible: each backend implements a subset of the problem classes, and an
unsupported pair is refused up front rather than failing later. Defaults are
`-c ./config/solver/muval_parallel_exc_tbq_ar.json` and `-p muclp`.

### Which invocation do I want?

The sections below are grouped by problem class, each with its backends. This table routes from
what you have to the `-p` name, the file extension, a typical configuration and the section:

| you have | `-p` | file | typical `-c` | section |
| --- | --- | --- | --- | --- |
| an **OCaml** program with refinement-type annotations | `ml` | `.ml` | `rcaml_pcsat_tbq_ar.json`, or a GSpacer/Spacer variant | [RCaml](#ocaml-programs-with-rcaml) |
| an **OCaml** program with algebraic effects | `ml` | `.ml` | `effcaml_*.json` | [EffCaml](#ocaml-programs-with-effcaml) |
| a **C** program and an LTL property | `cltl` | `.c` | `muval_parallel_exc_tbq_ar.json` | [C programs](#c-programs) |
| a **C** program and a CTL property | `cctl` | `.c` | as above | [C programs](#c-programs) |
| a **T2** transition system, asking termination / non-termination / safety / non-safety | `ltsterm`, `ltsnterm`, `ltssafe`, `ltsnsafe` (append `bv` for bit-vectors) | `.t2` | as above | [Labeled transition systems](#labeled-transition-systems) |
| the same, answered interactively | `ltsterminter` | `.t2` | `muval_interactive_*.json` | [Interactive mode](#interactive-conditional-non-termination-verification) |
| an **integer transition system** in the Termination Competition's SMT-LIB2 format, asking termination / non-termination | `pltsterm`, `pltsnterm` | `.smt2` | `muval_parallel_exc_tbq_ar.json`, `mustrat.json` | [Integer transition systems](#integer-transition-systems-of-the-termination-competition) |
| a **BTOR2** word-level hardware model, asking whether a bad state is reachable | `btor2` | `.btor2`, `.btor` | `mucyc.json`, `spacer.json`; the answer is the Hardware Model Checking Competition's (`sat` = a bad state is reachable) | [BTOR2](#btor2-hardware-models) |
| **constrained Horn clauses** or any class of the (D)QpCSP hierarchy | `chc`, `pcsp`, `qchc`, `dqchc`, `qechc`, `dqechc`, `qpcsp`, `dqpcsp`, `pfwcsp`, `pfwncsp` — **one problem class under many names** | `.smt2`, `.clp` | `pcsat_tbq_ar.json` | [CHC and its extensions](#chc-and-its-extensions) |
| the same, but maximizing an objective | `chcmax` | `.smt2` | `optpcsat_*.json` | [CHC maximization](#chc-maximization) |
| the same, solved by cyclic-proof search | `chc` | `.smt2` | `mucyc*.json` | [Other backends](#other-backends-mucyc-spacer-and-hoice) |
| a **SyGuS** synthesis problem (INV, CLIA, or a regular expression) | `sygus` | `.sl` | `pcsat_*.json` | [SyGuS](#syntax-guided-synthesis), [regular expressions](#regular-expression-synthesis) |
| a **fixpoint logic** formula (muArith, muCLP) | `muclp` | `.hes` | `muval_*.json`, `mucyc*.json`, `mustrat*.json` | [muArith and muCLP](#muarith-and-muclp) |
| the same, answered interactively | `muclpinter` | `.hes` | `muval_interactive_*.json` | [Interactive mode](#muval-interactive-conditional-mode) |
| a **quantified SMT** formula | `smt` | `.smt2` | `mucyc*.json`, `mustrat*.json`, `z3_smt.json` | [Quantified SMT](#quantified-smt) |
| a **probabilistic** fixpoint formula, or a pGCL / SGCL program | `qfl`, `pgcl`, `sgcl` | `.qhes`, `.pgcl`, `.sgcl` | `muval_*.json` | [QFL](#qfl), [pGCL and SGCL](#probabilistic-programs-pgcl-and-sgcl) |
| a **SAT / QSAT / DQSAT / HOSAT** instance | `sat`, `qsat`, `dqsat`, `hosat` | `.dimacs`, `.qdimacs`, `.dqdimacs`, `.hosat` | `dbg_homcsat.json` | [HOMCSat](#sat-qsat-dqsat-and-hosat-with-homcsat) |
| a **higher-order model checking** problem | `homc` | `.hrs`, `.hors`, `.hmtt`, `.ehmtt` | `horsat2.json`, `trecs.json` | [Higher-order model checking](#higher-order-model-checking) |
| a SAT/QSAT/HOSAT, SMT, CHC or pCSP, SyGuS, fixpoint-logic, C, transition-system or BTOR2 input, to be **printed** in the form a backend would receive rather than solved | as above | as above | `printer.json`, `printer_smt2.json` | [Printing](#printing-a-problem-instead-of-solving-it) |

The input is dispatched on its **extension**, so a file with the wrong one is refused rather than
guessed at. Two classes are accepted by the command line and implemented by no backend
(`ltsmucal`, `ltsrel`; see [Declared but not implemented](#declared-but-not-implemented)).

### Reading the answer

**Answers go to stdout and diagnostics to stderr**, so `2>/dev/null` leaves the result alone. The
forms differ by backend:

| form | example | meaning |
| --- | --- | --- |
| verdict and iteration count | `sat,2` | satisfiable, found after 2 CEGIS iterations |
| verdict, iterations, exchange counts | `valid,5,5\|2` | MuVal running its primal (prove) and dual (disprove) solvers in parallel: valid; 5 CEGIS iterations of **whichever side answered first** (the output does not say which, and a `valid` can come from either, the dual's refutation being flipped); the primal side sent bounds 5 times and the dual side 2 times |
| a word | `YES` / `NO` / `MAYBE` | for termination-style problems on labeled transition systems |
| `unknown`, `timeout` | | **ordinary answers, not errors** — the tool ran and did not decide |

The counts after a verdict are **not reproducible across runs of one binary**: every fresh variable
is drawn from one counter and collections of terms are ordered by the names inside them, so an
unrelated change, or simply the memory layout of the process, reorders what the SMT solver is asked
and it answers differently. On some inputs even the verdict is a draw — the run answers in seconds
or not at all. Treat the verdict as the result and the numbers as diagnostics. In the examples
below, an answer is shown as a comment on the line after its command.

Exit status is `0` when the tool produced an answer, including `unknown` and `timeout`. A non-zero
status means the tool itself failed; a run stopped by an external `timeout(1)` gives `124`.

### Configuration

**Behaviour is driven by the JSON configuration, not by command-line flags.** `config/solver/` holds
the entry points and each references the components it uses — a coordinator, a synthesizer, a
qualifier generator, a validator, a resolver, templates — so a configuration is a small tree of
files rather than one file.

A `dbg_` prefix means the same configuration with tracing switched on throughout its tree; the
`dbg_` PCSat configurations additionally check the solution they produce, re-verifying a model
against the original constraints and a refutation against its recorded derivations, and printing a
`(sat-check …)` or `(unsat-check …)` report. That is the way to ask the tool to check itself.

### Command-line flags

The only command-line flags beyond `-c`, `-p` and `-v` are four the configuration cannot express,
because the information is absent from the input rather than chosen:

* `--c-bound-wide-nondets` — bound the results of 32- and 64-bit `__VERIFIER_nondet_*` by their
  width in the C front end. Off by default because the bounds cost solver time and rarely matter, so
  a property that depends on the upper bound of an `int` needs it.
* `--bv-default WIDTH[s|u]` (default `32s`) — the width and signedness assumed for a bit-vector
  whose input states neither.
* `--btor2-witness stdout|PATH` — with `-p btor2`, write a counterexample in the BTOR2 witness
  format for a `sat` answer, either to standard output (where it replaces the `sat` line, which is
  its own first line) or to the file `PATH` (with `sat` on standard output); `btorsim -c MODEL
  WITNESS` checks it. Off by default, and then no witness is computed.
* `--btor2-witness-strict` — with `--btor2-witness`, print no answer rather than a `sat` whose
  witness cannot be built (an array value to write, a trace longer than 256 steps, a query the solver
  does not settle). `script/hwmcc/bin/` runs the tool this way as `<script> <model> <certificate>`.

`-v` turns on the **front-end** diagnostics (parsing, loading) and the banner; solver-internal
tracing is the `verbose` setting inside the configuration, which is what a `dbg_` configuration
sets. Neither implies the other.

## Program verification

### OCaml programs with RCaml

RCaml verifies an OCaml program by refinement type inference. Input: a `.ml` file, `-p ml`.

#### Safety verification

With PCSat:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

With GSpacer:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_gspacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

With Spacer:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_spacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

#### Temporal verification (constraint generation only)

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_temp_eff_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/temporal/sum_term.ml
```

### OCaml programs with EffCaml

EffCaml verifies an effectful OCaml program by higher-order model checking. Input: a `.ml` file,
`-p ml`. Build `horsat2` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_effcaml.json -p ml ./benchmarks/OCaml/oopsla24/mutable_set_not_b_false_UNSAT.ml
```

### C programs

A C program and a temporal property are reduced to fixpoint logic validity and checked by MuVal.
Input: a `.c` file, `-p cltl` (LTL) or `-p cctl` (CTL).

#### LTL verification

Build `ltl3ba` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cltl ./benchmarks/C/cav2015ltl/coolant/coolant_basis_1_safe_sfty.c
```

Please download and use the benchmark set of [Ultimate LTL Automizer](https://ultimate.informatik.uni-freiburg.de/downloads/ltlautomizer/).

`--c-bound-wide-nondets` bounds 32-/64-bit `__VERIFIER_nondet_*` results by their width. By
default an unsigned draw is only constrained by `x >= 0` and a signed one is unbounded, because the
width bounds cost solver time and rarely decide anything; a property that depends on the upper
bound of an `int` or `uint` needs the flag.

#### CTL verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p cctl ./benchmarks/C/pldi2013ctl/industrial/1-acqrel-AGimpAF-succeed.c
```

Please obtain and use the benchmark set from the following paper:
* Byron Cook and Eric Koskinen. Reasoning about nondeterminism in programs. PLDI 2013.

### Probabilistic programs (pGCL and SGCL)

A probabilistic or stochastic program is translated into a QFL problem and solved by MuVal<sup>QFL</sup>,
so the configurations are those of the [QFL](#qfl) section. Input: a `.pgcl` or `.sgcl` file, `-p pgcl` or
`-p sgcl`. The SGCL inputs are the benchmark set of Diabolo (https://github.com/fzaiser/diabolo;
Zaiser, Murawski and Ong, *Guaranteed Bounds on Posterior Distributions of Discrete Probabilistic
Programs with Loops*, POPL 2025), included as a submodule:
`git submodule update --init benchmarks/SGCL/diabolo`.

```bash
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg1.json -p sgcl ./benchmarks/SGCL/diabolo/benchmarks/geo.sgcl
# valid, ...
```

For `-p pgcl`, only a **bound** query — does the expected value stay within a stated bound, written
`?Ex [e] <= b` (or `<`, `>=`, `>`) at the end of the program — is reduced to a solvable problem.
The example asks whether the number of failures before a fair coin first succeeds has expectation
at most 1, which is exact:

```bash
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg1.json -p pgcl ./benchmarks/pGCL/simple/geometric_count_bound_valid.pgcl
# valid, ...
```

A program that asks for the expected value of an expression itself (`?Ex [e]`, or no query at all)
is reported as an unsupported query rather than silently producing nothing:

```bash
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg1.json -p pgcl ./benchmarks/pGCL/from_qhes/ert_random_walk.pgcl
# unsupported query: this pGCL program asks for the expected value of an expression,
# and only a bound query is reduced to a solvable problem
```

## Transition system verification

### Labeled transition systems

A T2 transition system is reduced to fixpoint logic validity and checked by MuVal. Input: a `.t2`
file, `-p ltsterm`, `ltsnterm`, `ltssafe`, `ltsnsafe` (and their `bv` forms) or `ltsterminter`.

#### Termination verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsterm ./benchmarks/LTS/simple/test.t2
```

#### Non-termination verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p ltsnterm ./benchmarks/LTS/simple/test.t2
```

#### Safety and non-safety verification

```bash
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_tbq_ar.json -p ltssafe ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# YES
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_tbq_ar.json -p ltsnsafe ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# NO
```

#### Bit-vector mode

Every class above has a bit-vector counterpart, named by appending `bv`: `ltstermbv`,
`ltsntermbv`, `ltssafebv`, `ltsnsafebv`, `ltsterminterbv`. The variables of a T2 file are then read
as fixed-width bit-vectors rather than as unbounded integers, so wraparound is modelled and a
property that holds over the integers may fail. A file that does not state a width is read at the
width `--bv-default` gives (`32s` unless set), because nothing can infer it.

```bash
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_tbq_ar.json -p ltstermbv ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# NO
```

#### Interactive conditional (non-)termination verification

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

#### Declared but not implemented

`-p ltsmucal` and `-p ltsrel` (and their `bv` forms) name problem classes — modal mu-calculus model
checking and relational verification over labeled transition systems — that the command line
accepts and no backend implements. They are refused up front with a message rather than failing
part way through.

### Integer transition systems of the Termination Competition

`-p pltsterm` (termination) and `-p pltsnterm` (non-termination) read an integer transition system
in the SMT-LIB2 format of the Termination Competition's ITS category: the program locations are
constants of a declared sort `Loc`, and `init_main` and `next_main` define the initial states and
the transition relation through `cfg_init` and `cfg_trans2`. The answer is `YES` when the property
is proved and `NO` when its negation is. The competition's inputs are the `benchmarks/term-comp`
submodule.

```bash
git submodule update --init benchmarks/term-comp
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_tbq_ar.json -p pltsterm ./benchmarks/term-comp/Integer_Transition_Systems/From_T2/florian.t2.smt2
# YES
./_build/default/main.exe -c ./config/solver/muval_parallel_exc_tbq_ar.json -p pltsnterm ./benchmarks/term-comp/Integer_Transition_Systems/From_T2/consts1nt.t2.smt2
# YES
./_build/default/main.exe -c ./config/solver/mustrat.json -p pltsterm ./benchmarks/term-comp/Integer_Transition_Systems/From_T2/florian.t2.smt2
# YES
```

### BTOR2 hardware models

A BTOR2 model (`.btor2` or `.btor`, `-p btor2`) is translated into CHC and solved by MuCyc, Spacer
or PCSat. The answer is the Hardware Model Checking Competition's: `sat` when a bad state is
reachable, `unsat` when none is. A model with a liveness (`justice`) property is refused as
unsupported input, and `fair` constraints without one are ignored. `--btor2-witness` (see
[Command-line flags](#command-line-flags)) also writes a counterexample trace.

```bash
./_build/default/main.exe -c ./config/solver/mucyc.json -p btor2 ./benchmarks/BTOR2/simple/counter_unsafe_sat.btor2
# sat
./_build/default/main.exe -c ./config/solver/spacer.json -p btor2 ./benchmarks/BTOR2/simple/counter_safe_unsat.btor2
# unsat
```

## Constraint solving

### CHC and its extensions

Constrained Horn clauses (CHC) and their extensions — $`\forall\exists`$CHC, $`\forall`$CHC,
pCSP, pfwnCSP and the (D)QpCSP hierarchy — are solved by PCSat. Input: a `.smt2` or `.clp` file.
`-p` accepts every class name of the (D)QpCSP hierarchy for this one problem class — `chc`,
`qchc`, `dqchc`, `qechc`, `dqechc`, `pcsp`, `qpcsp`, `dqpcsp` (also `q-pcsp`, `dq-pcsp`),
`pfwcsp`, `pfwncsp` — so a file can be run under the name of the class it belongs to; the name is
documentation, and the front end and solver do not differ.

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### Quantifiers in clauses

**Existentially quantified CHC** has a term variable quantified existentially in a head,
`forall x. B => exists y. H`. PCSat skolemises it and represents the witness as a *functional*
predicate (kind FN), which is what pfwCSP adds over pCSP — so the answer to the following command
reports `(kinds (FN 2))`, the two witnesses:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/ECHC/bar.smt2
```

**Universally quantified CHC** has an unknown in the scope of a `forall` in a *body*. It is the
same demand at the opposite polarity — `(forall y. phi) => H` is `(exists y. not phi) or H` — and
is discharged the same way, by skolemising into a functional predicate:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/UCHC/pred_poly_unknown_inst_sat.smt2
```

A quantifier inside a clause whose scope holds only universal symbols and theory atoms is
neither of these: it is an ordinary quantified *constraint*, and it is passed to the SMT
solver as it stands rather than skolemised. The second command below is a quantified /
dependently quantified pCSP:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/max.clp
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p dqpcsp ./benchmarks/DQpfwCSP/handcrafted/indirect_dependency.smt2
```

#### Universally quantified sorts and functions ((D)QpCSP)

A **QpCSP** quantifies sorts and functions universally in front of the unknowns, and a **DQpCSP**
additionally says, for each unknown, which universals it may depend on (Henkin quantification,
as in DQBF). Such a problem is **satisfiable when every interpretation of the universal sorts and
functions — a universal sort ranging over every non-empty set — and every model of the background
theory admits an interpretation of the unknowns that makes every assertion true**, an unknown seeing
only the universals of its dependency set. This is not plain SMT-LIB satisfiability, which asks for
*some* model. The forms the reader adds for it are below; `(set-logic QHORN)` and
`(set-logic DQHORN)` name the two classes and, like `HORN`, make every plain `declare-fun` an
unknown to solve for (under an ordinary SMT-LIB logic it is an uninterpreted symbol instead).

| form | meaning |
| --- | --- |
| `(declare-forall-sort a)` | a sort universally quantified over every non-empty set |
| `(declare-forall-sort a :min-card k)` | the same, plus `k` universal constants `#card_a_0` … `#card_a_{k-1}` of sort `a`, declared distinct as a premise of every later assertion that mentions one; the clauses may use these names |
| `(declare-forall-fun f (S1 … Sn) S)` | a universally quantified function (a predicate when `S` is `Bool`, a constant when there are no arguments) |
| `(declare-forall-fun f (S1 … Sn) S :law φ)` | the same, with the law `φ` inserted as a premise into every later assertion that reaches `f`, directly or through the definitions it applies; a law written with free variables is instantiated at the clause's variables of the same names, a closed one (with its own `forall`) is nested whole |
| `(declare-fun P (S1 … Sn) Bool)` | an unknown that depends on every `Bool`-valued `declare-forall-fun` declared before it, so declaration order is the quantifier prefix |
| `(declare-dep-exists-fun P (f1 … fk) (S1 … Sn) Bool)` | an unknown that depends on exactly the universals `f1 … fk` (of any result sort), which may be incomparable with another unknown's set |

The four examples below are, in order: two unknowns, each depending on a different universal
predicate; a universal sort with at least two elements; the same clauses without the distinctness
premise, which a one-element sort refutes; and a universal function with a law, reached through a
`define-fun`.

```bash
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p dqpcsp ./benchmarks/DQpCSP/handcrafted/dep_incomparable_slack_sat.smt2
# sat,0
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/card2_mincard_sugar_sat.smt2
# sat,0
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/card2_constants_nopremise_unsat.smt2
# unsat,0
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/law_through_define_fun_sat.smt2
# sat,0
```

The corpora are divided by class: `benchmarks/DQpCSP/handcrafted/` (universal sorts, functions
and dependency sets), `benchmarks/DQpfwCSP/` (a term variable quantified existentially in a head,
which leaves the (D)QpCSP class and is skolemised into functional predicates), `benchmarks/ECHC/`
and `benchmarks/UCHC/` (the existential-in-head and universal-in-body cases shown above). All of
them run under `-p pcsp` or any of its other names.

#### Predicate kinds

A **kind** is a condition on an individual solution of an unknown, which a CHC format has no place
for; the reader takes one declaration per kind, each declaring a `Bool`-valued unknown. Arguments
are written as for `declare-fun`; positions are 0-based.

| declaration | the solution `P` must be |
| --- | --- |
| `(declare-fnp P (S1 … Sn T) Bool)` | functional: for every `x̄` exactly one `y` with `P(x̄, y)` |
| `(declare-wfp R (S̄ S̄) Bool)` | well-founded: the relation `R(x̄, ȳ)` between the two halves of its arguments has no infinite chain |
| `(declare-dwfp R (S̄ S̄) Bool)` | disjunctively well-founded: contained in a finite union of well-founded relations |
| `(declare-totp (i1 … ik) P (S1 … Sn) Bool)` | total in positions `i1 … ik`: for every value of them some value of the others makes `P` true; `()` asks for non-emptiness |
| `(declare-nep P (S1 … Sn) Bool)` | non-empty; the same as `(declare-totp () P …)` |
| `(declare-uniqp j prov P (S1 … Sn) Bool)` | single-valued in position `j` (possibly partial); `prov` says why: `declared` (part of the problem), `entailed` (the clauses imply it in every solution), `least-model` (the clauses make the predicate single-valued in their least model) |
| `(declare-admp P …)`, `(declare-admcp P …)`, `(declare-integp P …)` | admissible (without and with conditioning) and integrable: the kinds RCaml's verification of higher-order probabilistic programs generates (ICFP 2024, in the References) |

Under `HORN`, a `declare-fun` with an `Int` or `Real` result is a function to synthesise, and a
nullary one of sort `RegLan` a regular expression (see [Regular expression
synthesis](#regular-expression-synthesis)).

The three examples below are, in order: `R(x, x - 1)` for `x > 0` is contained in a well-founded
relation; a relation forced to contain a 2-cycle is not well-founded; and a functional predicate
whose clause leaves two witnesses per argument.

```bash
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/wf_countdown_sat.smt2
# sat,1
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/wf_int_2cycle_unsat.smt2
# unsat,1
./_build/default/main.exe -c ./config/solver/pcsat_tbq_ar.json -p pcsp ./benchmarks/pfwnCSP/simple/fn_two_witness_window_sat.smt2
# sat,0
```

`benchmarks/pfwnCSP/simple/` has an input per kind, with the expected answer in its name. Not all
of them are answered within a minute by the default configuration (`ne_forced_total_sat`,
`tot_abs_witness_sat`, `dwf_two_cycle_sat` were not).

#### Candidate atoms

`(set-info :candidates (P ((x1 S1) … (xn Sn)) (A1 … Ak)))`, after `P` is declared, offers the
formulas `A1 … Ak` over `x1 … xn` as building blocks for `P`'s solution. They are hints: they are
never asserted and leave the set of solutions unchanged, and a solver that does not know the
keyword may skip it, since `set-info` with a keyword the standard does not define is standard
SMT-LIB.

#### Other backends: MuCyc, Spacer and HoIce

MuCyc solves CHC by cyclic-proof search. Its configurations, in the order of the commands below:

| configuration | file |
| --- | --- |
| `Ind(Ret(F, MBP(0)))` | `mucyc_returnF_mbp0_indNF.json` |
| `Ind(Yld(T, MBP(1)))` | `mucyc_yieldTT_mbp1_indNF.json` |
| `Ret(F, MBP(0))` | `mucyc_returnF_mbp0.json` |
| `Yld(T, MBP(1))` | `mucyc_yieldTT_mbp1.json` |
| `Solve` | `mucyc.json` |

```bash
./_build/default/main.exe -c ./config/solver/mucyc_returnF_mbp0_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
./_build/default/main.exe -c ./config/solver/mucyc_yieldTT_mbp1_indNF.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
./_build/default/main.exe -c ./config/solver/mucyc_returnF_mbp0.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
./_build/default/main.exe -c ./config/solver/mucyc_yieldTT_mbp1.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
./_build/default/main.exe -c ./config/solver/mucyc.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

The external solvers Spacer (inside Z3) and HoIce are wrapped for plain CHC (build `hoice` and
place it in the current directory for the second):

```bash
./_build/default/main.exe -c ./config/solver/spacer.json -p chc ./benchmarks/CHC/simple/sum.smt2
# sat
./_build/default/main.exe -c ./config/solver/hoice.json -p chc ./benchmarks/CHC/simple/sum.smt2
# sat
```

### CHC maximization

OptPCSat solves CHC while maximizing an objective. Input: a `.smt2` file, `-p chcmax`.

```bash
./_build/default/main.exe -c ./config/solver/dbg_optpcsat_nc_tbq_ar.json -p chcmax ./benchmarks/CHC/popl2023opt/test2.smt2
```

### Syntax-guided synthesis

PCSat solves SyGuS problems of the INV and CLIA tracks. Input: a `.sl` file, `-p sygus`.

```bash
git submodule update --init benchmarks/sygus-comp/
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p sygus ./benchmarks/sygus-comp/comp/2017/CLIA_Track/fg_max2.sl
```

### Regular expression synthesis

PCSat synthesises a regular expression declared as a nullary unknown of sort `RegLan`.

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp ./benchmarks/SyGuS/regex/ex1.smt2
```

## Fixpoint logic

### muArith and muCLP

Validity of a muArith or $`\mu`$CLP formula. Input: a `.hes` file, `-p muclp` (or `-p muclpinter`
for the interactive mode).

#### MuVal

MuVal runs in one of several modes, in the order of the commands below:

| mode | configuration |
| --- | --- |
| primal | `dbg_muval_prove_tbq_ar.json` |
| dual | `dbg_muval_disprove_tbq_ar.json` |
| parallel | `dbg_muval_parallel_tbq_ar.json` |
| parallel with clause exchange | `dbg_muval_parallel_exc_tbq_ar.json` |
| MuVal<sub>PPM</sub>, parallel with clause exchange | `dbg_muval_parallel_exc_ppm_tbq_ar.json` |

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_prove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_disprove_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl2b-invalid.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_parallel_exc_ppm_tbq_ar.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### MuVal, interactive conditional mode

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

#### MuStrat

```bash
./_build/default/main.exe -c ./config/solver/dbg_mustrat.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

### QFL

MuVal<sup>QFL</sup> checks QFL formulas. Input: a `.qhes` file, `-p qfl`. Build
`PolyQEnt` and place it to run as `./polyqent/PolyQEnt`.

#### Validity checking

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_quant_polyqent_deg3.json -p qfl ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
```

#### Almost-sure satisfiability checking of &omega;-regular properties

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_quant_polyqent_deg1.json -p qfl ./benchmarks/QFL/omega_regular/ex3_9.qhes
```

#### Upper bound checking of posterior distributions

```bash
./_build/default/main.exe -c ./config/solver/muval_quant_polyqent_deg1.json -p qfl ./benchmarks/QFL/distribution_bounds/threedim_deg2.qhes
```

### HFL and QHFL

Validity checking with MuVal<sup>HFL</sup> and MuVal<sup>QHFL</sup>; the example runs through the
OCaml front end (`-p ml`).

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_pcsat_tbq_ar.json -p ml ./benchmarks/OCaml/quantitative/icfp24/coin_flip_unif.ml
```

## SMT

### Quantified SMT

A quantified SMT formula. Input: a `.smt2` file, `-p smt`. A prefix may quantify over Bool, Int,
Real or bit-vectors; Bool combines with any one of the other three, but those three do not combine
with each other.

#### MuCyc

```bash
./_build/default/main.exe -c ./config/solver/mucyc_progress_ncr.json -p smt ./benchmarks/QSMT/max.smt2
```

#### MuStrat

```bash
./_build/default/main.exe -c ./config/solver/mustrat.json -p smt ./benchmarks/QSMT/max.smt2
```

#### Z3

```bash
./_build/default/main.exe -c ./config/solver/z3_smt.json -p smt ./benchmarks/QSMT/max.smt2
# sat
```

#### Bit-vectors

`benchmarks/QSMT/BV/` holds the bit-vector examples, with the expected answer in each file name.

```bash
./_build/default/main.exe -c ./config/solver/mucyc.json -p smt ./benchmarks/QSMT/BV/bv_add_inverse_sat.smt2
```

## Higher-order model checking and Boolean satisfiability

### Higher-order model checking

Input: a `.hrs`, `.hors`, `.hmtt` or `.ehmtt` file, `-p homc`. Two external checkers are wrapped,
and **they read different dialects of the same file extension**, distinguished by the automaton
section at the end of the file. TRecS reads a trivial tree automaton (`%BEGINA`); HorSat2 reads an
alternating one (`%BEGINR` together with `%BEGINATA`). Give a file to the other one and it says so
and exits non-zero, rather than reporting a failed verification. Build `trecs` or `horsat2` and
place it in the current directory.

An alternating automaton (`%BEGINR` + `%BEGINATA`) goes to HorSat2:

```bash
./_build/default/main.exe -c ./config/solver/horsat2.json -p homc ./benchmarks/HORS/AAAI2025/Schroder-Bernstein-theorem_ord2.hrs
```

A trivial one (`%BEGINA`) goes to TRecS; `.hmtt` (EHMTT) also goes to TRecS:

```bash
./_build/default/main.exe -c ./config/solver/trecs.json -p homc ./benchmarks/HORS/simple/loop_br_sat.hors
# sat
```

### SAT, QSAT, DQSAT and HOSAT with HOMCSat

HOMCSat reduces Boolean satisfiability to higher-order model checking. Input: a `.dimacs`,
`.qdimacs`, `.dqdimacs` or `.hosat` file, `-p sat`, `qsat`, `dqsat` or `hosat`. Build `horsat2` and
place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p sat ./benchmarks/SAT/easy2.dimacs
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p qsat ./benchmarks/QSAT/test.qdimacs
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p dqsat ./benchmarks/QSAT/test.qdimacs
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p dqsat ./benchmarks/QSAT/test.dqdimacs
./_build/default/main.exe -c ./config/solver/dbg_homcsat.json -p hosat ./benchmarks/HOSAT/AAAI2025/f_h-neq-g_h_ord3.hosat
# sat
```

The larger inputs under `benchmarks/HOSAT/AAAI2025/` take minutes: `cps-arity1_ord3.hosat` answers `sat`
in about 100 to 170 s.

For plain SAT the Z3 and MiniSat backends are wrapped as well:

```bash
./_build/default/main.exe -c ./config/solver/z3_sat.json -p sat ./benchmarks/SAT/easy2.dimacs
# sat
./_build/default/main.exe -c ./config/solver/minisat.json -p sat ./benchmarks/SAT/easy2.dimacs
# sat
```

## Printing a problem instead of solving it

The `Printer` backend reads an input as any other backend would, applies the preprocessing its
configuration names, and prints the resulting problem instead of solving it, which shows what a
solver is actually given. `printer_smt2.json` prints constraint problems as SMT-LIB2 (CHC with the
extensions above), `printer.json` in the tool's own notation; a transition system is printed as
the fixpoint-logic formula it is reduced to, and a SAT instance as the higher-order model checking
problem HOMCSat solves.

```bash
./_build/default/main.exe -c ./config/solver/printer_smt2.json -p chc ./benchmarks/CHC/simple/sum.smt2
./_build/default/main.exe -c ./config/solver/printer.json -p ltsterm ./benchmarks/LTS/simple/test.t2
```

## Artifacts

The directories below at the top of the repository each hold the artifact-evaluation instructions
(and usually a Dockerfile) of one paper. They build the current source, so a result may differ
from the archived artifact named in each README:

| directory | paper |
| --- | --- |
| `cav21ae_dt/` | Decision Tree Learning in CEGIS-Based Termination Analysis (CAV 2021) |
| `cav21ae_rel/` | Constraint-based Relational Verification (CAV 2021) |
| `popl24ae/` | Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers (POPL 2024) |
| `icfp24ae/` | Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System (ICFP 2024) |
| `oopsla25ae/` | On Higher-Order Model Checking of Effectful Answer-Type-Polymorphic Programs (OOPSLA 2025) |
| `cav26ae/` | Lagrangian-Based Duality for Quantified SMT Algorithms (CAV 2026) |
| `pldi26ae_lower/` | Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification (PLDI 2026) |
| `pldi26ae_omega/` | A Hierarchy of Supermartingales for ω-Regular Verification (PLDI 2026) |
| `popl27ae/` | Solving First-Order Fixed-Point Logics via a Least-to-Greatest Transformation Based on Game Semantics (POPL 2027) |

## References

### RCaml

1. Satoshi Kura, Marco Gaboardi, Taro Sekiyama, and Hiroshi Unno. A Category-Theoretic Framework for Dependent Effect Systems. ESOP 2026.

1. Taro Sekiyama and Hiroshi Unno. Algebraic Temporal Effects: Temporal Verification of Recursively Typed Higher-Order Programs. POPL 2025.

1. Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers. POPL 2024.

1. Taro Sekiyama and Hiroshi Unno. Temporal Verification with Answer-Effect Modification. POPL 2023.

1. Yoji Nanjo, Hiroshi Unno, Eric Koskinen, and Tachio Terauchi. A Fixpoint Logic and Dependent Effects for Temporal Property Verification. LICS 2018.

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

### MuVal

1. Satoshi Kura and Hiroshi Unno. Solving First-Order Fixed-Point Logics via a Least-to-Greatest Transformation Based on Game Semantics. POPL 2027.

1. Hiroshi Unno, Tachio Terauchi, Yu Gu, and Eric Koskinen. Modular Primal-Dual Fixpoint Logic Solving for Temporal Verification. POPL 2023.

1. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021.

### MuVal<sup>QFL</sup>

1. Kazuki Watanabe and Hiroshi Unno. Automated Safety Verification of Posterior Distributions of Probabilistic Programs. IJCAI 2026.

1. Satoshi Kura and Hiroshi Unno. A Hierarchy of Supermartingales for &omega;-Regular Verification. PLDI 2026.

1. Satoshi Kura, Hiroshi Unno, and Takeshi Tsukada. Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification. PLDI 2026.

### MuVal<sup>HFL</sup> & MuVal<sup>QHFL</sup>

1. Kazuki Watanabe, Mayuko Kori, Taro Sekiyama, Satoshi Kura, and Hiroshi Unno. A Categorical Product Construction for Temporal Verification of Effectful Higher-Order Programs. 2026.

1. Satoshi Kura and Hiroshi Unno. Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System. ICFP 2024.

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

We thank Ziteng Wang for contributing the Docker build workflow. We also thank Hiroyuki Katsura, Philippe Heim, Ehsan Goharshady, Elaine Li, Benedikt Maderbacher, Alvin George, and Moritz Leven Rosarius for reporting bugs in PCSat and MuVal. We are also grateful to the organizer of termCOMP 2023, Akihisa Yamada, and participants Florian Frohn and Nils Lommen, as thanks to them, we were able to identify a bug in MuVal. We further thank Florian Frohn, as the organizer of termCOMP 2025, for valuable feedback that helped improve the robustness of MuVal's C program (non-)termination verification. We also thank the artifact evaluation committees of POPL, PLDI, CAV, OOPSLA, and ICFP for their valuable feedback.
