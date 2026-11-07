# CoAR: Collection of Automated Reasoners

* RCaml: A refinement type checking and inference tool for OCaml
* EffCaml: A software model checker for effectful OCaml programs and for tree-processing programs written as extended higher-order multi-parameter tree transducers (EHMTT)
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
* [Program verification](#program-verification): OCaml programs, tree-processing programs (EHMTT, XML types), C programs (LTL and CTL; safety and termination through LLVM IR), probabilistic programs (pGCL and SGCL)
* [Transition system verification](#transition-system-verification): labeled transition systems (T2), integer transition systems of the Termination Competition, BTOR2 hardware models
* [Constraint solving](#constraint-solving): CHC and its extensions, CHC maximization, SyGuS, regular expressions
* [Fixpoint logic](#fixpoint-logic): muArith and muCLP, QFL, HFL and QHFL
* [SMT](#smt): quantified SMT
* [Higher-order model checking and Boolean satisfiability](#higher-order-model-checking-and-boolean-satisfiability): HORS, HOMCSat
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
| `horsat2` | higher-order model checking with HorSat2 (`horsat2.json`, EffCaml's `effcaml.json`) | `./horsat2` | https://github.com/hopv/horsat2 |
| `trecs` | higher-order model checking with TRecS (`trecs.json`, EffCaml's `effcaml_trecs.json`) | `./trecs` | |
| `ltl3ba` | LTL verification of C programs (`-p cltl`) | `./ltl3ba`, else `PATH` | https://sourceforge.net/projects/ltl3ba/ |
| `polyqent` | the QFL backend PolyQEnt | `./polyqent/PolyQEnt` (the `path` field of its config) | https://github.com/ChatterjeeGroup-ISTA/polyqent |
| `optimathsat` | bounds on posterior distributions in QFL, when enabled in the config | `./optimathsat.exe` | https://optimathsat.disi.unitn.it/ |
| `cvc5` | a second opinion only: the `check_solution` certificate check (off by default) runs on Z3 and asks cvc5 again about a constraint Z3 left undecided, and a few optional PCSat proof steps (off by default) ask it; without cvc5 such a constraint is reported unchecked, never failed | `./cvc5`, else `PATH` | https://cvc5.github.io/ |
| `clang`, `llvm2kittel` | scripts that translate C programs to T2 transition systems | as set in each script | https://clang.llvm.org/, https://github.com/addmai/llvm2kittel/tree/svcomp2026 |
| `clang` 19 | compiling a C program to the LLVM IR that `-p llvm*` and `llvm2lts` read | as set in each script | https://releases.llvm.org/ (19.1.7) |
| `llvm2lts` | the competition scripts' route from LLVM IR to a T2 transition system (see [C programs and LLVM IR](#c-programs-and-llvm-ir)) | as set in each script | built from `athena/llvm2lts` with `script/llvm2lts/dune.sh` |

The **LLVM 19 OCaml bindings** (opam `llvm` at `19-shared` against an installed LLVM 19, or `19-static`
against the static libraries of the LLVM 19.1.7 release, as the competition archive is built) are an
optional dependency. With them, `dune build` includes the LLVM IR frontend behind `-p llvmsafe`,
`llvmterm`, `llvmsafebv` and `llvmtermbv`; without them everything else builds, and those four problem
classes refuse every input with that reason. No other problem class needs LLVM.

### Benchmarks from other sources

Benchmark sets that other groups publish are not copied into this repository. Some are git
submodules under `benchmarks/` (the CHC-COMP, SyGuS-Comp, Termination Competition and SV-COMP
repositories, `CHC/hopv`, `CHC/ADTRem`, `SGCL/diabolo` and the sources of the C termination sets);
fetch one with `git submodule update --init <path>`. The others are downloaded from their
publishers by `script/fetch_benchmarks.sh`, which checks every file against a pinned checksum
(`script/fetch/<name>.manifest`) and applies the few local fixes to upstream files as patches
kept beside the manifests:

```bash
script/fetch_benchmarks.sh               # list the names, destinations and what is present
script/fetch_benchmarks.sh materialised  # every set the examples and scripts here read
script/fetch_benchmarks.sh cav2015ltl    # one set
script/fetch_benchmarks.sh --verify cav2015ltl
```

Some sets are generated from their sources rather than downloaded, because their publishers ship the
encoders and not the `.hes` files: `script/gen_issy_hes.py` encodes the infinite-state
reactive-synthesis benchmarks (the `benchmarks/infinite-state-reactive-synthesis-benchmarks`
submodule) with issy, Spot's `ltl2tgba` and `rpgencode` into `benchmarks/muCLP/issy`, and
`script/gen_sprout_hes.sh` builds SPROUT (the `benchmarks/sprout` submodule) with a small patch
that writes its muCLP instances instead of solving them. The protocols of Sprout(A) (its PLDI 2026
artifact) are fetched by `script/fetch_benchmarks.sh sprouta`, and `script/gen_sprouta_hes.sh` writes
their muCLP instances in the same way. Each script's header says which tools it needs.

### Optional: the MIP libraries

`lib/MIP` and `lib/MIPSolver` need the `lp` and `lp-glpk` opam packages (GLPK, free software), and
`lib/MIPSolver/gurobi` additionally `lp-gurobi`, which binds the commercial Gurobi solver. They are
optional dependencies of `CoAR.opam`, so `opam install . --deps-only` does not pull them in, and the
libraries are declared `(optional)`: without the packages `dune build` skips them and everything else
builds. Without `lp-gurobi`, `CoAR.MIPSolver` is built with GLPK only.

### With Docker

```bash
docker pull ghcr.io/hiroshi-unno/coar:main
```

or

```bash
sudo docker build -t coar .
```

The Dockerfile packages the CoAR executable, configurations, OCaml runtime library and Z3/Apron shared libraries. External backends such as Hoice, PolyQEnt, TRecS, HorSat2, OptiMathSAT and the standalone Z3 executable require separate installation. cvc5 is also omitted by default; add `--build-arg WITH_CVC5=1` to install its static release binary (version `CVC5_VERSION`, default 1.4.1) into `/root/coar`, which is on `PATH`.

This image (the root `Dockerfile`, tagged `coar` above and `coar:latest` by the competition builds) is built without LLVM 19's OCaml bindings, so the direct LLVM frontend is not in it and `-p llvmsafe`, `llvmsafebv`, `llvmterm` and `llvmtermbv` refuse every input. The competition images build CoAR again with the bindings (`llvm.19-static`): use `script/termcomp/Dockerfile` and its scripts (see "The competition scripts" below) for the direct route, or build CoAR yourself with the bindings installed.

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
unsupported pair is refused up front rather than failing later. The default `-p` is `muclp`; the
default `-c` depends on the problem class: `./config/solver/portfolio_muval_ppm_mustrat_muval_ppm.json`
(MuVal with the parity-progress-measure reduction for 10 s, then MuStrat for 60 s, then MuVal with that
reduction again) for `muclp` and `pltsterm`, the two classes it was measured on, and
`./config/solver/muval.json` for the others.

### Which invocation do I want?

The sections below are grouped by problem class, each with its backends. This table routes from
what you have to the `-p` name, the file extension, a typical configuration and the section:

| you have | `-p` | file | typical `-c` | section |
| --- | --- | --- | --- | --- |
| an **OCaml** program with refinement-type annotations | `ml` | `.ml` | `rcaml.json`, or a GSpacer/Spacer variant | [RCaml](#ocaml-programs-with-rcaml) |
| an **OCaml** program with algebraic effects | `ml` | `.ml` | `effcaml.json` (HorSat2), `effcaml_trecs.json` (TRecS) | [EffCaml](#ocaml-programs-with-effcaml) |
| a **C** program and an LTL property | `cltl` | `.c` | `muval.json` | [C programs](#c-programs) |
| a **C** program and a CTL property | `cctl` | `.c` | as above | [C programs](#c-programs) |
| **LLVM IR** compiled from a C program by clang 19, asking unreach-call safety or termination | `llvmsafe`, `llvmterm` (append `bv` for bit-vectors) | `.ll`, `.bc` | `muval_yesno.json` | [C programs and LLVM IR](#c-programs-and-llvm-ir) |
| a **C** program, asking unreach-call safety, termination or memory safety, read through LLVM IR in one command | `csafe`, `cterm`, `cmemsafe`, `cnooverflow`, `cmemcleanup`, `ctermmemsafe` | `.c`, `.i` | `athena.json` | [Athena inside CoAR](#athena-inside-coar-p-cterm-p-csafe) |
| a **C** program as the software-verification and termination competitions pose it (unreach-call, termination, overflow, memory safety) | a wrapper script, not `-p` | `.c`, `.i` | chosen by the script | [C programs and LLVM IR](#c-programs-and-llvm-ir) |
| a **T2** transition system, asking termination / non-termination / safety / non-safety, or whether every / some run visits its `BUCHI` locations infinitely often | `ltsterm`, `ltsnterm`, `ltssafe`, `ltsnsafe`, `ltsbuchi`, `ltsexbuchi` (append `bv` for bit-vectors) | `.t2` | as above | [Labeled transition systems](#labeled-transition-systems) |
| the same, answered interactively | `ltsterminter` | `.t2` | `muval_interactive_*.json` | [Interactive mode](#interactive-conditional-non-termination-verification) |
| an **integer transition system** in the Termination Competition's SMT-LIB2 format, asking termination / non-termination | `pltsterm`, `pltsnterm` | `.smt2` | `muval.json`, `mustrat.json` | [Integer transition systems](#integer-transition-systems-of-the-termination-competition) |
| a **BTOR2** word-level hardware model, asking whether a bad state is reachable | `btor2` | `.btor2`, `.btor` | `mucyc.json`, `spacer.json`; the answer is the Hardware Model Checking Competition's (`sat` = a bad state is reachable) | [BTOR2](#btor2-hardware-models) |
| **constrained Horn clauses** or any class of the (D)QpCSP hierarchy | `chc`, `pcsp`, `qchc`, `dqchc`, `qechc`, `dqechc`, `qpcsp`, `dqpcsp`, `pfwcsp`, `pfwncsp` — **one problem class under many names** | `.smt2`, `.clp` | `pcsat.json` | [CHC and its extensions](#chc-and-its-extensions) |
| the same, but maximizing an objective | `chcmax` | `.smt2` | `optpcsat_*.json` | [CHC maximization](#chc-maximization) |
| the same, solved by cyclic-proof search | `chc` | `.smt2` | `mucyc*.json` | [Other backends](#other-backends-mucyc-spacer-and-hoice) |
| a **SyGuS** synthesis problem (INV, CLIA, or a regular expression) | `sygus` | `.sl` | `pcsat_*.json` | [SyGuS](#syntax-guided-synthesis), [regular expressions](#regular-expression-synthesis) |
| a **fixpoint logic** formula (muArith, muCLP) | `muclp` | `.hes` | `muval_*.json`, `mucyc*.json`, `mustrat*.json` | [muArith and muCLP](#muarith-and-muclp) |
| the same, answered interactively | `muclpinter` | `.hes` | `muval_interactive_*.json` | [Interactive mode](#muval-interactive-conditional-mode) |
| a **quantified SMT** formula | `smt` | `.smt2` | `mucyc*.json`, `mustrat*.json`, `z3_smt.json` | [Quantified SMT](#quantified-smt) |
| a **probabilistic** fixpoint formula, or a pGCL / SGCL program | `qfl`, `pgcl`, `sgcl` | `.qhes`, `.pgcl`, `.sgcl` | `muval_*.json` | [QFL](#qfl), [pGCL and SGCL](#probabilistic-programs-pgcl-and-sgcl) |
| a **higher-order fixpoint** formula (HFL), or a quantitative one (QHFL) as an OCaml program in an expectation mode | `hfl`, `qhfl` | `.in`, `.hfl`, `.ml` (`hfl`); `.ml` (`qhfl`) | `muval_hfl.json`, `muval_qhfl.json` | [HFL and QHFL](#hfl-and-qhfl) |
| a **SAT / QSAT / DQSAT / HOSAT** instance | `sat`, `qsat`, `dqsat`, `hosat` | `.dimacs`, `.qdimacs`, `.dqdimacs`, `.hosat` | `dbg_homcsat.json` | [HOMCSat](#sat-qsat-dqsat-and-hosat-with-homcsat) |
| a **higher-order model checking** problem | `homc` | `.hrs`, `.hors` | `trecs.json`, `horsat2.json`, also `effcaml.json` | [Higher-order model checking](#higher-order-model-checking) |
| a **tree-processing program** written as an (extended) higher-order multi-parameter tree transducer | `homc` | `.hmtt`, `.ehmtt` | `effcaml.json`, `effcaml_trecs.json` | [EffCaml: tree-processing programs](#tree-processing-programs-with-effcaml) |
| an **XML type** (regular tree expression type definitions), to be **translated** into the tree automaton a `.hors`/`.hmtt` file takes | `xmltype` | `.xt` | `printer.json` (the only backend that accepts it) | [XML types as tree automata](#xml-types-as-tree-automata) |
| a SAT/QSAT/HOSAT, SMT, CHC or pCSP, SyGuS, fixpoint-logic (muCLP, QFL, pGCL, SGCL, HFL), C, transition-system or BTOR2 input, to be **printed** in the form a backend would receive rather than solved | as above | as above | `printer.json`, `printer_smt2.json` | [Printing](#printing-a-problem-instead-of-solving-it) |

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
| a verdict alone | `valid`, `sat` | backends that report no iteration count, such as MuStrat, MuCyc, Spacer and EffCaml |
| a word | `YES` / `NO` / `MAYBE` | for transition systems (`-p lts*`, `pltsterm`, `pltsnterm`), LLVM IR (`-p llvm*`) and C programs on Athena's route (`-p cterm`, `csafe`, ...) |
| `unknown`, `timeout` | | **ordinary answers, not errors** — the tool ran and did not decide |

A sequential portfolio configuration (`portfolio_*.json`, the default for `muclp` and `pltsterm`)
runs its stages one after another and prints exactly the line of the stage that answered, in that
backend's form.

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

The command-line flags beyond `-c`, `-p` and `-v` are six the configuration cannot express,
because the information is absent from the input rather than chosen, and one that names a second
configuration file:

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
* `--c-data-model LP64|ILP32` (default `LP64`) — with the C problems of Athena's route (`-p cterm`,
  `csafe`, `cmemsafe`, `cmemcleanup`, `cnooverflow`, `ctermmemsafe`), the data model the task states.
* `--c-signed-overflow wrap|undefined|arbitrary` — with `-p cterm`, `csafe`, `cmemsafe`, `cmemcleanup`
  or `ctermmemsafe`, what an overflowing signed operation yields, since the task does not state its
  compiler; it replaces the configuration's `signed_overflow`. `wrap`: the two's-complement value, as
  gcc and clang define it under `-fwrapv`; **an answer is then about the program built with
  `-fwrapv`** (an optimising build without it assumes signed overflow away). `undefined`: the
  execution stops there, SV-COMP's reading, which is also the answer for a build that traps on
  overflow. `arbitrary`: any value of the type, every choice covered (the direct route only); a `YES`
  then holds for every build in which an overflowing operation yields some value or ends the
  program, and a `NO` may rest on the values chosen, which a note on standard error says before solving. A YES for
  every compiler, optimising ones included, is overflow-freedom (`-p cnooverflow`, which reads no
  reading of overflow) together with `undefined`. Without the flag the configuration's reading
  holds (default: undefined). With `Mathematical` integers (the default configuration's), `wrap` reads
  them as `Wrapping`, since the mathematical reading has no wrap-around, and says so on standard error.
  Refused up front where it means nothing: with unbounded integers, `wrap` with `Auto` integers (the
  rewriting's per-program choice excludes wrapping signed arithmetic), `arbitrary` on the llvm2lts route.
* `--llvm-config PATH` — with `-p llvmsafe`, `llvmterm`, `llvmsafebv` or `llvmtermbv`, the LLVM IR
  frontend's own JSON configuration: how integers are read (mathematical, modulo 2^N, ...), what
  undefined behaviour does to an execution, the data model, and which LLVM passes run before the
  translation. The files are in `config/llvmfront/`; without the flag every field is at its default
  (`config/llvmfront/llvmfront.json` states them all).

`-v` turns on the **front-end** diagnostics (parsing, loading) and the banner; solver-internal
tracing is the `verbose` setting inside the configuration, which is what a `dbg_` configuration
sets. Neither implies the other.

## Program verification

### OCaml programs with RCaml

RCaml verifies an OCaml program by refinement type inference. Input: a `.ml` file, `-p ml`.

**What its answer means.** `sat` means the annotated refinement types are derivable, so the program
meets its specification. `unsat` means the refinement-type constraints generated from the program have
no solution: **no refinement typing exists for the annotation in RCaml's type system**. That is not a
proof that the program violates its specification, because the type system is incomplete -- for
example, mutable references are not tracked flow-sensitively, and an invariant that needs an
existential over a list's elements is out of reach. This is the convention of the POPL 2024 paper
(Kawamata, Unno, Sekiyama, Terauchi), whose table reports such safe-but-untypable programs as not
verified; `benchmarks/OCaml/popl24/arm/bfs-SAT.ml` is one, answered `unsat`. Under a configuration that
assumes functions cannot fail (`cgen_config` fields `never_fail`, `can_fail_only_at_total_apps` or
`can_cause_temp_eff_only_at_total_apps`: the `rcaml_*no_fail*`, `rcaml_*no_part*` and `rcaml_temp_eff_*`
configs), an `unsat` is reported as `unknown`: those options look only for typings of a restricted shape
(every function argument refined by `true`, for instance), and that none exists does not show that no typing
does -- `benchmarks/OCaml/safety/simple/function_precondition_assert_sat.ml` is typable, but not with its
function's argument refined by `true`.

#### Safety verification

With PCSat:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

With GSpacer:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_gspacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

With Spacer:

```bash
./_build/default/main.exe -c ./config/solver/dbg_rcaml_wopp_spacer.json -p ml ./benchmarks/OCaml/safety/simple/sum.ml
```

#### Temporal verification

The temporal effects of recursive functions are least and greatest fixpoint predicates. With
`rcaml_temp_eff_muval.json` the generated constraints become a fixpoint-logic validity problem, which MuVal solves.
A proof is answered `sat`. A refutation is answered `unknown`, because traces, their concatenation and
regular-expression membership are uninterpreted for the solver. A problem whose shape the translation cannot
take is printed and answered `unknown`, as `rcaml_temp_eff.json` answers every temporal problem.

```bash
./_build/default/main.exe -c ./config/solver/rcaml_temp_eff_muval.json -p ml ./benchmarks/OCaml/temporal/simple/recursive_callee_terminates_sat.ml
```

#### Relational verification by induction, with lemmas

`rcaml_mucyc_relational.json` checks a program whose property is an `assert` in `main` (no `[@@@assert]`
needed) by the relational proof search of MuCyc: induction over the least fixpoints of the functions'
graphs (Unno, Torii and Sakamoto, CAV 2017). A property relating functions can also be stated directly, and a
lemma the proof needs is stated the same way, both about the file's top-level functions by application:

```ocaml
[@@@property "forall x y r1 r2. mult x y = r1 => mult_c x y = r2 => r1 = r2"]
[@@@lemma "forall x y r. mult x y = r => mult (x - 1) y = r - y"]
```

The formula is OCaml expression syntax (integers, constructors, `+ - * / mod`, comparisons, `&&`, `||`,
`not`, `<=>`) with `=>` for implication and an optional `forall` prefix. An equation `f a1 ... an = t` whose
other side is not an application says that `f a1 ... an` can evaluate to `t`; any other application stands for
each value it returns, so an application without a value makes its atom vacuous. A property is a goal and may
mention an application's value only as a premise (`f x = r => ...`). A function applied to fewer or more
arguments than it takes, or a name that is not a top-level function (a parameter, a local, a library
function), is refused: a lemma with a line on stderr, a property by stopping. **A lemma is a claim, never an
assumption**: the search first proves it by the same rules, using only the lemmas proved before it, and uses it
only then; each one's outcome is a line on stderr. A lemma about `f` speaks about `f`'s whole graph: it is
proved about an instance of `f` that admits every argument and reaches the copies the program uses through the
proved fact that each is contained in it. A call can be labelled, `(f a1 ... an [@copy lbl])`, and the notation
then names that call's copy: `f@lbl` is `f` restricted to the arguments of that call and of the recursive calls it
starts, and `called f@lbl a1 ... an` holds of exactly those argument tuples -- for a loop written as a
tail-recursive function, its reachable states. `f@def` names the whole graph, as `f` does.

```ocaml
let mult_c x y = (loop y x y 0 [@copy entry])
[@@@lemma "forall c x y r. called loop@entry c x y r => c >= 1 => called loop@entry (c - 1) x (y - 1) r"]
```

A label no call carries, a label not on a call of a top-level function, a label written on two calls, and `called`
of an unlabelled function are refused with a line on stderr. An attribute RCaml does not read (`[@@@types]`,
`[@@@hccs]`, `[@@@option]` of other tools) is named once on stderr and ignored.

A question that needs predicates of its own -- such as a loop given as Horn clauses rather than as a function --
is stated as a block of Horn clauses over the file's functions, `[@@@chc "..."]`: each clause `p a1 ... an :- body.`
(or the fact `p a1 ... an.`) defines an auxiliary predicate `p`, and each query `?- body.` is a goal, answered `sat`
when no query body holds of the least predicates the clauses define. A body is a formula of the notation above in
which an auxiliary predicate applied to its arguments is an atom; every variable of a clause is universal in it,
and a lemma may speak about the block's predicates. A predicate named like a top-level function, and a file with
two blocks, are refused.

```ocaml
[@@@chc
"i c x y r :- c = y && r = 0.
 i c' x y r' :- c' = c - 1 && r' = r + x && i c x y r && c <> 0.
 mult_c x y r :- i 0 x y r.
 ?- mult x y = r1 && mult_c x y r2 && r1 <> r2."]
[@@@lemma "forall c x y r. i c x y r => c >= 1 => i (c - 1) x (y - 1) r"]
```

```bash
./_build/default/main.exe -c ./config/solver/rcaml_mucyc_relational.json -p ml ./benchmarks/OCaml/relational/simple/mult_commutative_with_lemma_true_sat.ml
# sat,-1  @assert type_of(main) <: int -> int -> unit [#1]
```

### OCaml programs with EffCaml

EffCaml verifies an effectful OCaml program by higher-order model checking. Input: a `.ml` file,
`-p ml`. The program's specification is an alternating tree automaton (`[@@@check_toplevel "..."]`), and the
model checker is the one EffCaml's `solver` field names:

- `effcaml.json` checks with HorSat2, which reads the alternating automaton as it is (several rules for one state
  and terminal joined into one disjunction); build `horsat2` and place it in the current directory.
- `effcaml_trecs.json` checks with TRecS, which takes only a deterministic trivial automaton: each transition's
  disjuncts become trivial transitions, and a specification is checked only when that gives one transition per
  state and terminal; otherwise (a disjunction, as an `if` or a boolean operator's specification usually has) the
  problem is refused with the state and terminal named, as is a disjunct that puts two states on one child (every
  annotated program under `benchmarks/OCaml` is refused so, at `q0 if`). Build `trecs` and place it in the current
  directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_effcaml.json -p ml ./benchmarks/OCaml/oopsla24/mutable_set_not_b_false_UNSAT.ml
./_build/default/main.exe -c ./config/solver/effcaml.json -p ml ./benchmarks/OCaml/oopsla24/file_SAT.ml
# sat
```

### Tree-processing programs with EffCaml

EffCaml also verifies tree-processing programs written as extended higher-order multi-parameter tree transducers
(EHMTT): a program over input and output trees, with a tree automaton and a type for each function stating which
trees it may receive and must return (the method of the APLAS 2010 and POPL 2010 papers in the references). Input: a `.hmtt` or `.ehmtt` file, `-p homc`, with EffCaml's configuration.
The program is reduced to higher-order model checking problems with a trivial tree automaton, checked by the model
checker EffCaml's `solver` field names: HorSat2 under `effcaml.json`, after each problem is translated into the
equivalent one with an alternating automaton and without finite data, and TRecS under `effcaml_trecs.json`, which
reads the problems as they are; build `horsat2` (or `trecs`) and place it in the current directory. The
reduction is EffCaml's alone: TRecS's and HorSat2's own configurations decide HORS problems and refuse an EHMTT,
naming the EffCaml configuration that uses that checker. EffCaml also takes a `.hrs`/`.hors` HORS problem and
hands it to the checker its `solver` names, as [below](#higher-order-model-checking).

```bash
./_build/default/main.exe -c ./config/solver/effcaml.json -p homc ./benchmarks/EHMTT/aplas2010/isort_sat.hmtt
# sat
```

An EHMTT is reduced to several HORS problems: `main` (the whole program) and one `coerceN` per coercion; it is
`sat` when every one is satisfied. This proves the output safety property, without guaranteeing eventual
output. The reduction is sound but incomplete: a rejected HORS problem can be a false alarm, for example when
repeated inspections of one input tree lose their correlation (see the APLAS 2010 and POPL 2010 references). So a
rejection is answered `unsat` only when the reduction is complete for the program (syntactically linear, no
coercion, no `gen`, a deterministic output automaton) or when running the program on concrete inputs confirms the
violation; otherwise the answer is `unknown`, and the checker's counterexample goes to standard error marked as
possibly spurious.
The input file name `-` reads standard input, which is always taken to be an
EHMTT (`cat f.hmtt | ./_build/default/main.exe -c ./config/solver/effcaml.json -p homc -`). Two fields of `ehmtt`
in the EffCaml config, read whichever checker its `solver` names, change what a run does besides the verdict:

```json
[ "EffCaml", { "ehmtt": { "check_all_problems": true, "hors_dir": "out" } } ]
```

A `sat` answer holds for every program. The reduction is complete only for a linear program (no input tree
case-analysed twice, a copy being a case analysis) without coercions and with a deterministic output automaton
(the POPL 2010 paper's Theorem 4.3), so a refutation is answered `unsat` only when the tool can establish that
(by a syntactic sufficient condition for linearity). Otherwise the tool runs the program, under the papers'
call-by-name semantics, on the input trees the input automaton accepts, smallest first and up to fixed bounds: when
some output is rejected, or a coercion is applied to a tree outside its language, the answer is `unsat` and stderr
names the inputs and the violation; when the search finds nothing, or cannot run the program (a `gen`, or a main type
with a function-typed parameter), the answer is `unknown`, and the checker's counterexample is printed on stderr
marked as possibly spurious.

`check_all_problems` (default `false`: stop at the first problem not satisfied) checks every problem and reports
each one's outcome, with the checker's counterexample, on stderr; the verdict on stdout is the same either way.
`hors_dir` (default none) writes every generated problem into that directory as `main.hors`, `coerce1.hors`, ...,
in TRecS's dialect, before any translation for HorSat2.
With `verbose` set, the reduction's statistics (order, sizes, rule and state counts, times) go to stderr.

#### XML types as tree automata

Input: a `.xt` file, `-p xmltype`, with the printer configuration; nothing is solved. The file is a sequence
of regular tree expression type definitions (EffCaml's XML-type front end), the first of
which is the start type: an upper-case name is a type, `label[...]` an element with its content, `,`
a sequence, `|` a choice, `*` and `?` repetition and option, `()` the empty sequence.

```
type Xhtml  = html[head[meta[]*,title[],meta[]*],body[Blocks]]
type Blocks = (h1[]|p[]|div[Blocks])*
```

Stars and options are eliminated and the result is printed as a trivial tree automaton accepting the trees of
the start type in the binary first-child/next-sibling encoding (`leaf` ends a sequence; `q0` is the initial
state), in the `%BEGINA` syntax that `.hors` and `.hmtt` files use, so it can be pasted into one as its input or
output automaton:

```bash
./_build/default/main.exe -c ./config/solver/printer.json -p xmltype ./benchmarks/EHMTT/xmltype/xhtmlmini.xt
# %BEGINA
# q0 html -> q4 q3.
# q1 leaf -> .
# ...
# %ENDA
```

A syntax error is reported as `error: <file>:<line>:<column>: ...` with status 1, as are an empty file, a type
defined twice and a reference to an undefined type.

An `.hmtt` file can take such type definitions directly, in a `%BEGINX ... %ENDX` section in place of its
`%BEGINA ... %ENDA` section; the type names are then the automaton's states, so the `%BEGINT` specification and
`coerce` (and `gen`) name types:

```
%BEGING
S x -> Appendix (coerce Doc (F x (a leaf leaf))) leaf.
...
%ENDG

%BEGINX
type Doc    = doc[Preface, (Div|P|Note)*]
...
type Xhtml  = html[head[meta[]*,title[],meta[]*],body[Blocks]]
type Blocks = (h1[]|h2[]|h3[]|h4[]|h5[]|h6[]|h7[]|h8[]|h9[]|p[]|b[]|div[Blocks])*
%ENDX

%BEGINT
S : Doc -> Xhtml.
%ENDT
```

The section is read when the file is (`/* */` and `(* *)` comments both work in it; a `%ENDX` inside a `(* *)`
comment ends it), and its syntax errors give the `.hmtt` file's own line and column. The automaton checked is what `-p xmltype`
prints for the definitions, with a state for every type: definitions that refer to one another form one schema,
each schema is translated separately (as if each were its own `.xt` file), and the schemas' automata are put side by
side. The model checkers see the state of type `T` as `qT`, since their automaton syntax reads a capitalised name as
a non-terminal. A file with both a `%BEGINA` and a `%BEGINX` section, a type name that the section does not define,
and a type name in a file with a `%BEGINA` section are refused with a message naming the file. Only automata in the
first-child/next-sibling encoding can be written this way: an input whose symbols are unary (`a*b*e` over `a -> q.`)
or nullary other than `leaf` (`qBool true -> .`) keeps its `%BEGINA` section.

```bash
./_build/default/main.exe -c ./config/solver/effcaml.json -p homc ./benchmarks/EHMTT/xmltype/gapid_html_xml_types_nonlinear_sat.hmtt
# sat
```

### C programs

A C program and a temporal property are reduced to fixpoint logic validity and checked by MuVal.
Input: a `.c` file, `-p cltl` (LTL) or `-p cctl` (CTL).

#### LTL verification

Build `ltl3ba` and place it in the current directory.

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval.json -p cltl ./benchmarks/C/cav2015ltl/coolant/coolant_basis_1_safe_sfty.c
```

The benchmark set of [Ultimate LTL Automizer](https://github.com/ultimate-pa/ultimate/tree/dev/trunk/examples/LTL)
(the CAV 2015 evaluation) is not shipped; `script/fetch_benchmarks.sh cav2015ltl` places it under
`benchmarks/C/cav2015ltl` from a pinned commit of the Ultimate repository.

`--c-bound-wide-nondets` bounds 32-/64-bit `__VERIFIER_nondet_*` results by their width. By
default an unsigned draw is only constrained by `x >= 0` and a signed one is unbounded, because the
width bounds cost solver time and rarely decide anything; a property that depends on the upper
bound of an `int` or `uint` needs the flag.

#### CTL verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval.json -p cctl ./benchmarks/C/pldi2013ctl/industrial/1-acqrel-AGimpAF-succeed.c
```

Please obtain and use the benchmark set from the following paper:
* Byron Cook and Eric Koskinen. Reasoning about nondeterminism in programs. PLDI 2013.

### C programs and LLVM IR

Safety (no call of `reach_error` is reachable) and termination of a C program, in the form the
software-verification (SV-COMP) and termination (termCOMP) competitions pose them, are checked by
compiling the program to LLVM IR and turning that into a problem MuVal solves. There are three
routes from LLVM IR to MuVal, and the C front end of [C programs](#c-programs) is a fourth route
from C that does not go through LLVM. The whole of the first two, from the C program on, also
runs inside CoAR as one command ([Athena inside CoAR](#athena-inside-coar-p-cterm-p-csafe)):

| route | entry | from LLVM IR to MuVal | external tools | LLVM 19 bindings in CoAR | status |
| --- | --- | --- | --- | --- | --- |
| direct | `-p llvmsafe`, `-p llvmterm` (`llvmsafebv`, `llvmtermbv` for bit-vectors) on a `.ll` or `.bc` file | CoAR reads the IR itself and builds a muCLP problem | clang 19 | **needed** | the termCOMP script's route for its categories `C`, `C_Mod` and `C_BV` |
| llvm2lts | `script/termcomp/solver_llvm2lts.sh` | the separate program `llvm2lts` writes a T2 transition system, which CoAR reads with `-p ltssafe`, `ltsterm` or `ltstermbv` | clang 19, `llvm2lts` | not needed | the route of `script/termcomp/solver_llvm2lts.sh` |
| llvm2kittel | the termCOMP script | `llvm2kittel` writes a T2 transition system, read as above | clang and `opt` of LLVM 3.6.2, `llvm2kittel` | not needed | the termCOMP script's `C_assume` and memory-safety categories |
| C front end | `-p cltl`, `-p cctl` on a `.c` file | no LLVM IR: the C program is read directly into muCLP | `ltl3ba` for `cltl` | not needed | LTL and CTL properties only ([C programs](#c-programs)) |

`llvm2lts` is a program of its own for the scripts: its source is in `athena/llvm2lts`,
`script/llvm2lts/dune.sh` builds it, and CoAR sees only the T2 file it writes. A CoAR built with the
LLVM 19 OCaml bindings also has it inside, for Athena's route below.
The direct route is the only route that needs CoAR to be built with the
LLVM 19 OCaml bindings (see [External tools](#external-tools-optional)).

Before compiling, the termCOMP scripts rewrite the C program into C whose pointers and heap
blocks are arrays (Ptr2Arr). There are two such C-to-C steps: the
original tool (`athena/Ptr2Arr`; for modular integers followed by `athena/SemanticAugmentor`, and on
the llvm2kittel route for bit-vectors `athena/TypeAnnotator` annotates the T2 file with types), and
a rewrite built on Frama-C (`athena/Ptr2ArrFC`), used on the llvm2lts and direct
routes.

#### The direct route

`-p llvmterm` checks termination of `main` and `-p llvmsafe` that no call of `reach_error` (or
`__VERIFIER_error`) is reachable; the answer is `YES` (the property holds), `NO` (it does not) or
`MAYBE`. An input with a construct the translation does not support is answered `MAYBE`, with the
reason on standard error. The IR must come from clang 19 **with debug information** (`-g`; a module
without it is refused). The scripts compile at `-O0` with clang's `optnone` marking switched off,
so that the frontend's own passes may run, and with `-fno-finite-loops`, so that a loop without side
effects is not assumed to terminate:

```bash
clang-19 -S -emit-llvm -g -O0 -Xclang -disable-O0-optnone -fno-finite-loops -ffp-contract=off \
  ./benchmarks/C/termcomp2026/non-guard_partition.c -o /tmp/non-guard_partition.ll
./_build/default/main.exe -c ./config/solver/muval_yesno.json -p llvmterm /tmp/non-guard_partition.ll
# YES
```

Integers are read as mathematical integers by default; `--llvm-config ./config/llvmfront/modulo.json`
reads them modulo 2^N, `unbounded.json` gives them no range at all, a `__VERIFIER_nondet_*` value
included (termCOMP's reading of C), and the `bv` problem classes read every value as a bit-vector of its
width. A program that uses pointers or the heap should go through a Ptr2Arr step first, as the
scripts below do.

#### Athena inside CoAR (`-p cterm`, `-p csafe`)

An Athena configuration (`config/solver/athena*.json`) runs the scripts' route from a C program to a
verdict in one command: the Frama-C rewriting (`athena/Ptr2ArrFC`), clang 19, llvm2lts or the direct
translation, then MuVal. `-p cterm` checks termination and `-p csafe` unreach-call safety; the
answer is `YES`, `NO` or `MAYBE` (with the reason on standard error when a step declines the
program), and `--c-data-model ILP32` reads a program of the 32-bit data model (default LP64):

```bash
./_build/default/main.exe -c ./config/solver/athena.json -p cterm ./benchmarks/C/termcomp2026/non-guard_partition.c
```

`athena.json` takes the llvm2lts route and reads integers as mathematical integers bounded by their
type; `athena_mod.json`, `athena_bv.json` and `athena_auto.json` read them modulo 2^N, as bit-vectors,
or as the rewriting chooses per program, and `athena_direct*.json` take the direct route. A
configuration also names clang (`clang`, default `clang-19` on the `PATH`; it also preprocesses a `.c` input
unless `preprocessor` is `Gcc`, so clang is the only compiler the route runs), the MuVal configuration
(`solver`) and where to keep the intermediate files (`work_dir`; by default they are removed). The
rewriting needs CoAR to be built with Frama-C 33 (opam `frama-c`), and the translations with the LLVM
19 OCaml bindings; a CoAR built without one refuses the route, naming what is missing. `-p cltl` and
`-p cctl` keep reading C with the C front end, a different method: the same program can get two
correct, different answers, since Athena reads C's integers with their width.

Further problem classes use checks of the rewriting. `-p cnooverflow` asks whether a signed
operation can overflow, and `-p cmemcleanup` whether every allocated block is freed (valid-memcleanup). `-p cmemsafe` asks whether a
memory-safety violation (an invalid dereference or free, and a leak as `memtrack` says) is
reachable. `-p ctermmemsafe` asks termination of a program without such a violation, as termCOMP's
`C_MemorySafety` category does: termination with every violation ending the execution, and memory
safety, are solved side by side by two runs of CoAR; the answer is the termination answer, or
`UNSAFE` when a violation is reachable (llvm2lts route only). Further fields select termCOMP's
reading of C (`"integers": ["Unbounded"]`: mathematical integers, any value for a nondeterministic
one), the rewriting's unbounded regions, llvm2lts's hoisting and the assumption of memory safety for
`-p cterm`; `script/termcomp/solver_llvm2lts.sh` writes
such a configuration for each task.

#### The competition scripts

`script/termcomp/solver.sh` (termCOMP) runs a whole route from a C file. It expects the layout of the
competition image (`script/termcomp/Dockerfile`), where every tool above is installed, so it is run
inside it, for example as

```bash
solver --category=C task.c
```

`script/termcomp/solver_llvm2lts.sh` runs the llvm2lts route on its own. `script/termcomp/README.md`
describes building the image.

### Probabilistic programs (pGCL and SGCL)

A probabilistic or stochastic program is translated into a QFL problem and solved by MuVal<sup>QFL</sup>,
so the configurations are those of the [QFL](#qfl) section. Input: a `.pgcl` or `.sgcl` file, `-p pgcl` or
`-p sgcl`. The SGCL inputs are the benchmark set of Diabolo (https://github.com/fzaiser/diabolo;
Zaiser, Murawski and Ong, *Guaranteed Bounds on Posterior Distributions of Discrete Probabilistic
Programs with Loops*, POPL 2025), included as a submodule:
`git submodule update --init benchmarks/SGCL/diabolo`.

```bash
./_build/default/main.exe -c ./config/solver/muval_qfl_polyqent_deg1.json -p sgcl ./benchmarks/SGCL/diabolo/benchmarks/geo.sgcl
# valid, ...
```

For `-p pgcl`, only a **bound** query — does the expected value stay within a stated bound, written
`?Ex [e] <= b` (or `<`, `>=`, `>`) at the end of the program — is reduced to a solvable problem.
The example asks whether the number of failures before a fair coin first succeeds has expectation
at most 1, which is exact:

```bash
./_build/default/main.exe -c ./config/solver/muval_qfl_polyqent_deg1.json -p pgcl ./benchmarks/pGCL/simple/geometric_count_bound_valid.pgcl
# valid, ...
```

A program that asks for the expected value of an expression itself (`?Ex [e]`, or no query at all)
is reported as an unsupported query rather than silently producing nothing:

```bash
./_build/default/main.exe -c ./config/solver/muval_qfl_polyqent_deg1.json -p pgcl ./benchmarks/pGCL/from_qhes/ert_random_walk.pgcl
# unsupported query: this pGCL program asks for the expected value of an expression,
# and only a bound query is reduced to a solvable problem
```

## Transition system verification

### Labeled transition systems

A T2 transition system is reduced to fixpoint logic validity and checked by MuVal. Input: a `.t2`
file, `-p ltsterm`, `ltsnterm`, `ltssafe`, `ltsnsafe`, `ltsbuchi`, `ltsexbuchi` (and their `bv` forms) or `ltsterminter`.
In these names `n` marks the negated question (`ltsnsafe` asks whether some run reaches the error location, the
negation of `ltssafe`; `ltsnterm` whether some run does not terminate), while `ex` in `ltsexbuchi` marks the
existential question (whether some run visits the Büchi locations infinitely often), which is not the negation of
`ltsbuchi`: both can answer NO, when some runs visit them infinitely often and others do not.

#### Termination verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval.json -p ltsterm ./benchmarks/LTS/simple/test.t2
```

#### Non-termination verification

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval.json -p ltsnterm ./benchmarks/LTS/simple/test.t2
```

#### Safety and non-safety verification

```bash
./_build/default/main.exe -c ./config/solver/muval.json -p ltssafe ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# YES
./_build/default/main.exe -c ./config/solver/muval.json -p ltsnsafe ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# NO
```

#### Büchi verification

A T2 file in the dialect of LTL-VerP (Chatterjee et al., FM 2024) names a set of Büchi locations in a
`BUCHI: {l1, l2, ...};` line after `START`, and may restrict the initial states with `PRE: {condition};`
(a `CUTPOINT: {...};` list there is read and ignored). `-p ltsbuchi` answers YES when every run visits
those locations infinitely often, `-p ltsexbuchi` when some run does; a run is infinite, so a state
without a successor ends none. An LTL property is checked on the product of the program with a Büchi
automaton: that of the property with `ltsbuchi` (exact for a deterministic automaton), that of its
negation with `ltsexbuchi` (YES refutes the property). In this dialect `/` divides exactly by a
constant (`b := (1/2) * b` has no successor from an odd `b`), as LTL-VerP reads it; the field
`t2_division` of the MuVal and MuStrat configurations chooses `["Exact"]` (the default), `["Truncate"]`
(T2's integer division) or `["Refuse"]`. A T2 file without a `BUCHI` line always truncates.

```bash
./_build/default/main.exe -c ./config/solver/muval.json -p ltsbuchi ./benchmarks/LTS/simple/buchi_branch_univ_no_ex_yes.t2
# NO
./_build/default/main.exe -c ./config/solver/muval.json -p ltsexbuchi ./benchmarks/LTS/simple/buchi_branch_univ_no_ex_yes.t2
# YES
```

#### Bit-vector mode

Every class above has a bit-vector counterpart, named by appending `bv`: `ltstermbv`,
`ltsntermbv`, `ltssafebv`, `ltsnsafebv`, `ltsbuchibv`, `ltsexbuchibv`, `ltsterminterbv`. The variables of a T2 file are then read
as fixed-width bit-vectors rather than as unbounded integers, so wraparound is modelled and a
property that holds over the integers may fail. A file that does not state a width is read at the
width `--bv-default` gives (`32s` unless set), because nothing can infer it.

```bash
./_build/default/main.exe -c ./config/solver/muval.json -p ltstermbv ./benchmarks/LTS/fse2022/C_BV/Adding_Subtracting_Zero_1_NT_annotated.t2
# NO
```

#### Interactive conditional (non-)termination verification

```bash
./_build/default/main.exe -c ./config/solver/muval_prove.json -p ltsterminter ./benchmarks/LTS/simple/prog2.t2
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
./_build/default/main.exe -c ./config/solver/muval.json -p pltsterm ./benchmarks/term-comp/Integer_Transition_Systems/From_T2/florian.t2.smt2
# YES
./_build/default/main.exe -c ./config/solver/muval.json -p pltsnterm ./benchmarks/term-comp/Integer_Transition_Systems/From_T2/consts1nt.t2.smt2
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
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p pcsp ./benchmarks/CHC/simple/sum.smt2
```

#### Quantifiers in clauses

**Existentially quantified CHC** has a term variable quantified existentially in a head,
`forall x. B => exists y. H`. PCSat skolemises it and represents the witness as a *functional*
predicate (kind FN), which is what pfwCSP adds over pCSP — so the answer to the following command
reports `(kinds (FN 2))`, the two witnesses:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p pcsp ./benchmarks/ECHC/bar.smt2
```

**Universally quantified CHC** has an unknown in the scope of a `forall` in a *body*. It is the
same demand at the opposite polarity — `(forall y. phi) => H` is `(exists y. not phi) or H` — and
is discharged the same way, by skolemising into a functional predicate:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p pcsp ./benchmarks/DQpfwCSP/pred_poly_unknown_inst_sat.smt2
```

A quantifier inside a clause whose scope holds only universal symbols and theory atoms is
neither of these: it is an ordinary quantified *constraint*, and it is passed to the SMT
solver as it stands rather than skolemised. The second command below is a quantified /
dependently quantified pCSP:

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p pcsp ./benchmarks/pfwnCSP/simple/max.clp
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p dqpcsp ./benchmarks/DQpfwCSP/handcrafted/indirect_dependency.smt2
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
./_build/default/main.exe -c ./config/solver/pcsat.json -p dqpcsp ./benchmarks/DQpCSP/handcrafted/dep_incomparable_slack_sat.smt2
# sat,0
./_build/default/main.exe -c ./config/solver/pcsat.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/card2_mincard_sugar_sat.smt2
# sat,0
./_build/default/main.exe -c ./config/solver/pcsat.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/card2_constants_nopremise_unsat.smt2
# unsat,0
./_build/default/main.exe -c ./config/solver/pcsat.json -p qpcsp ./benchmarks/DQpCSP/handcrafted/law_through_define_fun_sat.smt2
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
./_build/default/main.exe -c ./config/solver/pcsat.json -p pcsp ./benchmarks/pfwnCSP/simple/wf_countdown_sat.smt2
# sat,1
./_build/default/main.exe -c ./config/solver/pcsat.json -p pcsp ./benchmarks/pfwnCSP/simple/wf_int_2cycle_unsat.smt2
# unsat,1
./_build/default/main.exe -c ./config/solver/pcsat.json -p pcsp ./benchmarks/pfwnCSP/simple/fn_two_witness_window_sat.smt2
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

#### Lemmas for the relational proof search

`(set-info :coar-lemma (forall ((x Int) ...) phi))`, after the predicates `phi` names are declared, states a
lemma about the least solution, for MuCyc's relational proof search (`mucyc_relational.json`) only; the
named form `(define-fun L ((x Int) ...) Bool phi)` with `(set-info :coar-lemma L)` means the same. **A lemma
is a claim, never an assumption**: the search proves it before using it and drops it otherwise, reporting
each outcome on stderr, so a false lemma can cost time but never an answer. Every other solver ignores it,
and both forms are standard SMT-LIB that other solvers may skip (z3 prints an error line for the first form's
s-expression value and goes on; it accepts the second silently).

```bash
./_build/default/main.exe -c ./config/solver/mucyc_relational.json -p pcsp ./benchmarks/CHC/relational/simple/mult_commutative_with_lemma_sat.smt2
# sat
```

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
./_build/default/main.exe -c ./config/solver/dbg_optpcsat_nc_pcsat_improver.json -p chcmax ./benchmarks/CHC/popl2023opt/test2.smt2
```

### Syntax-guided synthesis

PCSat solves SyGuS problems of the INV and CLIA tracks. Input: a `.sl` file, `-p sygus`.

```bash
git submodule update --init benchmarks/sygus-comp/
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p sygus ./benchmarks/sygus-comp/comp/2017/CLIA_Track/fg_max2.sl
```

### Regular expression synthesis

PCSat synthesises a regular expression declared as a nullary unknown of sort `RegLan`.

```bash
./_build/default/main.exe -c ./config/solver/dbg_pcsat.json -p pcsp ./benchmarks/SyGuS/regex/ex1.smt2
```

## Fixpoint logic

### muArith and muCLP

Validity of a muArith or $`\mu`$CLP formula. Input: a `.hes` file, `-p muclp` (or `-p muclpinter`
for the interactive mode).

A `.hes` file may open with SMT-LIB `declare-datatypes`/`declare-datatype` commands. A datatype's
name is then a sort (`(l: L)`), its constructors and selectors are applied like predicates
(`cons x l`, `hd l`; a constructor without fields is a constant; an application binds tighter than
every operator, so `hd l >= 1` and `p = cons x l` need no parentheses), and `is_C t` tests for the
constructor `C` unless a predicate of that name is defined. Parametric datatypes are not supported
(`benchmarks/muCLP/simple/datatype_list_*.hes`). The printer (`-c config/solver/printer.json`) writes the
declarations back, so a printed problem reads back. Independently of datatypes, a quantifier stands only at the
start of a formula or inside parentheses: `n >= 0 => (exists (l: L). Len l n)` reads, and the same
without the parentheses is a syntax error.

#### MuVal

MuVal runs in one of several modes, in the order of the commands below:

| mode | configuration |
| --- | --- |
| primal | `dbg_muval_prove.json` |
| dual | `dbg_muval_disprove.json` |
| parallel with clause exchange | `dbg_muval.json` |
| MuVal<sub>PPM</sub>, parallel with clause exchange | `dbg_muval_ppm.json` |

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_prove.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_disprove.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl2b-invalid.hes
./_build/default/main.exe -c ./config/solver/dbg_muval.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
./_build/default/main.exe -c ./config/solver/dbg_muval_ppm.json -p muclp ./benchmarks/muCLP/popl2023mod/sas2019_ctl1.hes
```

#### MuVal, interactive conditional mode

```bash
./_build/default/main.exe -c ./config/solver/muval_prove.json -p muclpinter ./benchmarks/muCLP/popl2023mod/sas2019_lines1.hes
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
./_build/default/main.exe -c ./config/solver/dbg_muval_qfl_polyqent_deg3.json -p qfl ./benchmarks/QFL/ert_random_walk_2nd_lb.qhes
```

#### Almost-sure satisfiability checking of &omega;-regular properties

```bash
./_build/default/main.exe -c ./config/solver/dbg_muval_qfl_polyqent_deg1.json -p qfl ./benchmarks/QFL/omega_regular/ex3_9.qhes
```

#### Upper bound checking of posterior distributions

```bash
./_build/default/main.exe -c ./config/solver/muval_qfl_polyqent_deg1.json -p qfl ./benchmarks/QFL/distribution_bounds/threedim_deg2.qhes
```

### HFL and QHFL

Validity checking with MuVal<sup>HFL</sup> (`-p hfl`) and MuVal<sup>QHFL</sup> (`-p qhfl`), both by
RCaml's refinement type inference.

`-p hfl` reads a higher-order fixpoint formula over the integers: a hierarchical equation system
(`%HES`) in a `.in` or `.hfl` file, in the dialects of ReTHFL, HFLMC2 and MuHFL (the configuration
field `dialect` restricts it to one), or its OCaml representation in a `.ml` file with
`[@@@mode "hfl_prop_as_bool"]`. The answer is `valid`, `invalid` or `unknown`, followed by the
iteration count. A system that mixes greatest and least fixpoints is refused.
`benchmarks/HFL/simple/` has an input per case, with the expected answer in its name.

```bash
./_build/default/main.exe -c ./config/solver/muval_hfl.json -p hfl ./benchmarks/HFL/simple/sum_valid.in
```

`-p qhfl` reads a quantitative HFL problem, which has no text syntax of its own: an OCaml program in
one of RCaml's expectation modes (`[@@@mode "hfl_prop_as_expectation"]`, for instance) whose
`[@@@assert]`s bound its top-level names. Each assertion is answered on a line of its own, `valid`
when the typing proves the bound and `unknown` otherwise; a file without an expectation mode is
refused. The benchmarks of the ICFP 2024 paper are such programs:

```bash
./_build/default/main.exe -c ./config/solver/muval_qhfl.json -p qhfl ./benchmarks/OCaml/quantitative/icfp24/coin_flip_unif.ml
```

## SMT

### Quantified SMT

A quantified SMT formula. Input: a `.smt2` file, `-p smt`. A prefix may quantify over Bool, Int,
Real or bit-vectors; Bool combines with any one of the other three, but those three do not combine
with each other.

#### MuCyc

```bash
./_build/default/main.exe -c ./config/solver/mucyc_qsat_deepest_own_projected_repeatedly.json -p smt ./benchmarks/QSMT/max.smt2
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

Input: a `.hrs` or `.hors` file, `-p homc`. Two external checkers of higher-order recursion schemes
(HORS) are wrapped, TRecS and HorSat2; an `.hmtt`/`.ehmtt` program is not a HORS problem, and both
refuse it, naming EffCaml's configuration for it ([above](#tree-processing-programs-with-effcaml)).
A file specifies its property in one of two automaton dialects, told apart by the automaton section
at its end: a trivial tree automaton (`%BEGINA`), which TRecS reads natively, or an alternating one
(`%BEGINR` together with `%BEGINATA`), which HorSat2 reads natively. Either checker accepts either
dialect, within its input class: the wrapper translates the other one exactly (a trivial automaton,
finite data included, into an alternating one for HorSat2; an alternating one into a trivial one for
TRecS, refusing a transition whose disjunct puts two states on one child). TRecS's input class is a
**deterministic** trivial automaton (its documentation says so, and its counterexample search follows
only the first transition of each state and terminal), so a trivial automaton with two transitions for
one state and terminal -- given, or produced by the translation from a disjunction -- is refused under
TRecS with that pair named; HorSat2 takes it. HorSat2 likewise reads only the first `%BEGINATA` rule
for a state and terminal, so several rules for one pair are joined into one disjunction, which means
the same, before it sees them. `effcaml.json` and `effcaml_trecs.json` take a HORS problem too and
hand it to HorSat2 and TRecS respectively.
Build `trecs` or `horsat2` and place it in the current directory.

An alternating automaton (`%BEGINR` + `%BEGINATA`), with HorSat2:

```bash
./_build/default/main.exe -c ./config/solver/horsat2.json -p homc ./benchmarks/HORS/AAAI2025/Schroder-Bernstein-theorem_ord2.hrs
```

A trivial one (`%BEGINA`), with TRecS (or with HorSat2, after the translation):

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
the fixpoint-logic formula it is reduced to, a pGCL or SGCL program as the QFL problem it is
reduced to (in the `.qhes` syntax of `-p qfl`), and a SAT instance as the higher-order model checking
problem HOMCSat solves. An HFL input (`-p hfl`) is printed as an HES (`printer.json`,
`printer_hfl_rethfl.json`), as its OCaml representation (`printer_hfl_ocaml.json`) or, at order 1,
as a muCLP (`printer_hfl_muclp.json`).

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

1. Satoshi Kura, Marco Gaboardi, Taro Sekiyama, and Hiroshi Unno. A Category-Theoretic Framework for Dependent Effect Systems. ESOP 2026. DOI: [10.1007/978-3-032-22720-1_15](https://doi.org/10.1007/978-3-032-22720-1_15)

1. Taro Sekiyama and Hiroshi Unno. Algebraic Temporal Effects: Temporal Verification of Recursively Typed Higher-Order Programs. POPL 2025. DOI: [10.1145/3704914](https://doi.org/10.1145/3704914)

1. Fuga Kawamata, Hiroshi Unno, Taro Sekiyama, and Tachio Terauchi. Answer Refinement Modification: Refinement Type System for Algebraic Effects and Handlers. POPL 2024. DOI: [10.1145/3633280](https://doi.org/10.1145/3633280)

1. Taro Sekiyama and Hiroshi Unno. Temporal Verification with Answer-Effect Modification. POPL 2023. DOI: [10.1145/3571264](https://doi.org/10.1145/3571264)

1. Yoji Nanjo, Hiroshi Unno, Eric Koskinen, and Tachio Terauchi. A Fixpoint Logic and Dependent Effects for Temporal Property Verification. LICS 2018. DOI: [10.1145/3209108.3209204](https://doi.org/10.1145/3209108.3209204)

1. Hiroshi Unno, Yuki Satake, and Tachio Terauchi. Relatively Complete Refinement Type System for Verification of Higher-Order Non-deterministic Programs. POPL 2018. DOI: [10.1145/3158100](https://doi.org/10.1145/3158100)

1. Kodai Hashimoto and Hiroshi Unno. Refinement Type Inference via Horn Constraint Optimization. SAS 2015. DOI: [10.1007/978-3-662-48288-9_12](https://doi.org/10.1007/978-3-662-48288-9_12)

1. Hiroshi Unno, Tachio Terauchi, and Naoki Kobayashi. Automating Relatively Complete Verification of Higher-Order Functional Programs. POPL 2013. DOI: [10.1145/2429069.2429081](https://doi.org/10.1145/2429069.2429081)

1. Hiroshi Unno and Naoki Kobayashi. Dependent Type Inference with Interpolants. PPDP 2009. DOI: [10.1145/1599410.1599445](https://doi.org/10.1145/1599410.1599445)

1. Hiroshi Unno and Naoki Kobayashi. On-Demand Refinement of Dependent Types. FLOPS 2008. DOI: [10.1007/978-3-540-78969-7_8](https://doi.org/10.1007/978-3-540-78969-7_8)

### EffCaml

1. Taro Sekiyama, Ugo Dal Lago, and Hiroshi Unno. On Higher-Order Model Checking of Effectful Answer-Type-Polymorphic Programs. OOPSLA 2025. DOI: [10.1145/3763184](https://doi.org/10.1145/3763184)

1. Taro Sekiyama and Hiroshi Unno. Higher-Order Model Checking of Effect-Handling Programs with Answer-Type Modification. OOPSLA 2024. DOI: [10.1145/3689805](https://doi.org/10.1145/3689805)

1. Hiroshi Unno, Naoshi Tabuchi, and Naoki Kobayashi. Verification of Tree-Processing Programs via Higher-Order Model Checking. APLAS 2010. DOI: [10.1007/978-3-642-17164-2_22](https://doi.org/10.1007/978-3-642-17164-2_22)

1. Naoki Kobayashi, Naoshi Tabuchi, and Hiroshi Unno. Higher-Order Multi-Parameter Tree Transducers and Recursion Schemes for Program Verification. POPL 2010. DOI: [10.1145/1706299.1706355](https://doi.org/10.1145/1706299.1706355)

### Thrust

1. Hiromi Ogawa, Taro Sekiyama, and Hiroshi Unno. Thrust: A Prophecy-based Refinement Type System for Rust. PLDI 2025. DOI: [10.1145/3729333](https://doi.org/10.1145/3729333)

### Athena

1. Negar Fathi, Hiroshi Unno, Tachio Terauchi, and Rahul Purandare. Sound Termination and Non-Termination Analysis of C Programs with Bit-Precise Bounded Semantics and Advanced Constructs. FSE 2026. DOI: [10.1145/3808205](https://doi.org/10.1145/3808205)

### PCSat & OptPCSat

1. Yu Gu, Takeshi Tsukada, and Hiroshi Unno. Optimal CHC Solving via Termination Proofs. POPL 2023. DOI: [10.1145/3571214](https://doi.org/10.1145/3571214)

1. Hiroshi Unno, Tachio Terauchi, and Eric Koskinen. Constraint-based Relational Verification. CAV 2021. DOI: [10.1007/978-3-030-81685-8_35](https://doi.org/10.1007/978-3-030-81685-8_35)

1. Yuki Satake, Hiroshi Unno, and Hinata Yanagi. Probabilistic Inference for Predicate Constraint Satisfaction. AAAI 2020. DOI: [10.1609/aaai.v34i02.5526](https://doi.org/10.1609/aaai.v34i02.5526)

### MuVal

1. Satoshi Kura and Hiroshi Unno. Solving First-Order Fixed-Point Logics via a Least-to-Greatest Transformation Based on Game Semantics. POPL 2027. arXiv: [2607.10650](https://arxiv.org/abs/2607.10650)

1. Hiroshi Unno, Tachio Terauchi, Yu Gu, and Eric Koskinen. Modular Primal-Dual Fixpoint Logic Solving for Temporal Verification. POPL 2023. DOI: [10.1145/3571265](https://doi.org/10.1145/3571265)

1. Satoshi Kura, Hiroshi Unno, and Ichiro Hasuo. Decision Tree Learning in CEGIS-Based Termination Analysis. CAV 2021. DOI: [10.1007/978-3-030-81688-9_4](https://doi.org/10.1007/978-3-030-81688-9_4)

### MuVal<sup>QFL</sup>

1. Kazuki Watanabe and Hiroshi Unno. Automated Safety Verification of Posterior Distributions of Probabilistic Programs. IJCAI 2026. DOI: [10.24963/ijcai.2026/91](https://doi.org/10.24963/ijcai.2026/91)

1. Satoshi Kura and Hiroshi Unno. A Hierarchy of Supermartingales for &omega;-Regular Verification. PLDI 2026. DOI: [10.1145/3808257](https://doi.org/10.1145/3808257)

1. Satoshi Kura, Hiroshi Unno, and Takeshi Tsukada. Supermartingales for Unique Fixed Points: A Unified Approach to Lower Bound Verification. PLDI 2026. DOI: [10.1145/3808348](https://doi.org/10.1145/3808348)

### MuVal<sup>HFL</sup> & MuVal<sup>QHFL</sup>

1. Kazuki Watanabe, Mayuko Kori, Taro Sekiyama, Satoshi Kura, and Hiroshi Unno. A Denotational Product Construction for Temporal Verification of Effectful Higher-Order Programs. 2026. arXiv: [2510.11320](https://arxiv.org/abs/2510.11320)

1. Satoshi Kura and Hiroshi Unno. Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System. ICFP 2024. DOI: [10.1145/3674662](https://doi.org/10.1145/3674662)

### MuCyc

1. Ivana Bocevska, Takeshi Tsukada, Hiroshi Unno, Oded Padon, and Sharon Shoham. Lagrangian-Based Duality for Quantified SMT Algorithms. CAV 2026. DOI: [10.1007/978-3-032-32526-6_4](https://doi.org/10.1007/978-3-032-32526-6_4)

1. Takeshi Tsukada and Hiroshi Unno. Inductive Approach to Spacer. PLDI 2024. DOI: [10.1145/3656457](https://doi.org/10.1145/3656457)

1. Takeshi Tsukada and Hiroshi Unno. Software Model-Checking as Cyclic-Proof Search. POPL 2022. DOI: [10.1145/3498725](https://doi.org/10.1145/3498725)

1. Hiroshi Unno, Sho Torii, and Hiroki Sakamoto. Automating Induction for Solving Horn Clauses. CAV 2017. DOI: [10.1007/978-3-319-63390-9_30](https://doi.org/10.1007/978-3-319-63390-9_30)

### MuStrat

1. Takeshi Tsukada, Hiroshi Unno, Oded Padon, and Sharon Shoham. A Primal-Dual Perspective on Program Verification Algorithms. POPL 2025. DOI: [10.1145/3704904](https://doi.org/10.1145/3704904)

### HOMCSat

1. Hiroshi Unno, Takeshi Tsukada, and Jie-Hong Roland Jiang. Solving Higher-Order Quantified Boolean Satisfiability via Higher-Order Model Checking. AAAI 2025. DOI: [10.1609/aaai.v39i11.33237](https://doi.org/10.1609/aaai.v39i11.33237)

## Acknowledgements

We thank Ziteng Wang for contributing the Docker build workflow. We also thank Hiroyuki Katsura, Philippe Heim, Ehsan Goharshady, Elaine Li, Benedikt Maderbacher, Alvin George, and Moritz Leven Rosarius for reporting bugs in PCSat and MuVal. We are also grateful to the organizer of termCOMP 2023, Akihisa Yamada, and participants Florian Frohn and Nils Lommen, as thanks to them, we were able to identify a bug in MuVal. We further thank Florian Frohn, as the organizer of termCOMP 2025, for valuable feedback that helped improve the robustness of MuVal's C program (non-)termination verification. We also thank the artifact evaluation committees of POPL, PLDI, CAV, OOPSLA, and ICFP for their valuable feedback.
