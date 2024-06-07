# ICFP24 Artifact Evaluation


## Basic Information

- Artifact URL: The artifact is available at [https://doi.org/10.5281/zenodo.11499237](https://doi.org/10.5281/zenodo.11499237)
- Paper: Satoshi Kura and Hiroshi Unno. Automated Verification of Higher-Order Probabilistic Programs via a Dependent Refinement Type System. ICFP 2024.

## Instructions for Artifact Evaluation

We will explain how to reproduce the experimental result (Table 2) in our paper.

### Files

We provide a docker image and the source code.
Make sure that you have downloaded (either of) the following files from [https://doi.org/10.5281/zenodo.11499237](https://doi.org/10.5281/zenodo.11499237).
- A Docker image `coar-icfp24ae.tar`
- The source code `coar-icfp24ae-src.zip`

The source code is also available from our [GitHub repository](https://github.com/hiroshi-unno/coar).

### Installation

You can choose one of the following options.

#### Option 1: Loading Docker Image
To load the docker image, run the following command:
```
sudo docker load -i coar-icfp24ae.tar
```

#### Option 2: Building Docker Image
Run the following command:
```
# Unzip the source code
unzip coar-icfp24ae-src.zip

# Go to the `icfp24ae` directory in the source code
cd path/to/the/source/code
cd icfp24ae

# Build the Docker image
sudo docker build -f Dockerfile -t coar-icfp24ae ../
```

Note that if your machine doesn't have sufficient memory, the build process might be "Killed" and fail.
In this case, try to increase the memory allocated for Docker.

### Running Experiments

If you are using Docker, start a new container:
```
sudo docker run --rm -it coar-icfp24ae:latest /bin/bash --login
```

Go to the top directory of our artifact and run `./icfp24ae/run.sh`:
```
cd ~/coar
./icfp24ae/run.sh
```

This script runs our tool against benchmarks in `benchmarks/OCaml/probabilistic/`.
After executing the script, you will find the output in `result.txt` at the top directory.


As a reference, we got the following result in approximately 20 minutes:

```
lics16_rec3.ml
TIMEOUT
299.986s

lics16_rec3_ghost.ml
sat,5   	@assert type_of(rec3) <: {$v807: real | $v807 = real(1)} -> (unit -> {$v805: real | $v805 = real(1)}) -> {$v800: real | real(0) <=. $v800 /\ $v800 <=. real(2) /. real(3)} [#1]
1.313s

lics16_coins.ml
sat,13   	@assert type_of(coins) <: (($x927:int) -> ($x931:int) -> {$v935: real | $x927 = $x931 /\ $v935 = real(1) \/ $x927 != $x931 /\ $v935 = real(0)}) -> {$v926: real | $v926 = real(1/2)} [#1]
2.657s

random_walk.ml
sat,19   	@assert type_of(f) <: {$v682: int | $v682 = 1} -> (unit -> {$v680: real | $v680 = real(0)}) -> {$v675: real | real(0) <=. $v675 /\ $v675 <=. real(3)} [#1]
3.690s

random_walk_unif.ml
sat,32   	@assert type_of(rw) <: {$v554: real | $v554 = real(1)} -> (unit -> {$v552: real | $v552 = real(0)}) -> {$v547: real | real(0) <=. $v547 /\ $v547 <=. real(6)} [#1]
6.774s

coin_flip.ml
sat,4   	@assert type_of(f) <: unit -> (unit -> {$v367: real | $v367 = real(0)}) -> {$v362: real | real(0) <=. $v362 /\ $v362 <=. real(1)} [#1]
0.558s

coin_flip_unif.ml
sat,5   	@assert type_of(f) <: unit -> (unit -> {$v389: real | $v389 = real(0)}) -> {$v384: real | real(0) <=. $v384 /\ $v384 <=. real(1)} [#1]
0.613s

icfp21_walk.ml
sat,0   	@assert type_of(geo) <: int -> (int -> {$v1027: real | $v1027 = real(0)}) -> {$v1022: real | real(0) <=. $v1022 /\ $v1022 <=. real(1)} [#1]
sat,12   	@assert type_of(randomWalk) <: ($x1808:int) -> (int -> {$v1821: real | $v1821 = real(0)}) -> {$v1816: real | real(0) <=. $v1816 /\ $v1816 <=. real(3) *. to_real (abs $x1808)} [#2]
5.774s

icfp21_coupons.ml
TIMEOUT
299.997s

lics16_fact.ml
sat,21   	@assert type_of(fact) <: ($x847:{$v862: int | $v862 >= 0}) -> (int -> {$v860: real | $v860 = real(0)}) -> {$v855: real | real(0) <=. $v855 /\ $v855 <=. real(1) +. to_real $x847 /. (real(2) -. real(5) /. real(6))} [#1]
5.231s

coin_flip_ord2.ml
sat,14   	@assert type_of(f) <: unit -> (unit -> {$v905: real * real | $v905 = (real(0):real,real(0):real)}) -> {$v898: real * real | real(0) <=. t_sel.0 $v898 /\ t_sel.0 $v898 <=. real(1) /\ real(0) <=. t_sel.1 $v898 /\ t_sel.1 $v898 <=. real(3)} [#1]
1.226s

coin_flip_ord3.ml
sat,56   	@assert type_of(f) <: unit -> (unit -> {$v1647: real * real * real | $v1647 = (real(0):real,real(0):real,real(0):real)}) -> {$v1639: real * real * real | real(0) <=. t_sel.0 $v1639 /\ t_sel.0 $v1639 <=. real(1) /\ real(0) <=. t_sel.1 $v1639 /\ t_sel.1 $v1639 <=. real(3) /\ real(0) <=. t_sel.2 $v1639 /\ t_sel.2 $v1639 <=. real(13)} [#1]
7.044s

toplas18_ex4.4.ml
TIMEOUT
300.027s

two_coin_conditioning.ml
sat,2   	@assert type_of(diverge) <: unit -> (unit -> real * real) -> {$v128: real * real | t_sel.0 $v128 = real(0) /\ t_sel.1 $v128 = real(1)} [#1]
sat,6   	@assert type_of(f) <: unit -> (unit -> {$v1046: real * real | t_sel.0 $v1046 = real(1) /\ t_sel.1 $v1046 = real(1)}) -> {$v1039: real * real | real(0) <=. t_sel.0 $v1039 /\ t_sel.0 $v1039 <=. real(1/2) *. t_sel.1 $v1039 /\ real(0) <=. t_sel.1 $v1039 /\ t_sel.1 $v1039 <=. real(1)} [#2]
0.975s

```

### Comparing Results

We explain how to compare the output of our artifact (`result.txt`) and the experimental result shown in our paper (Table 2).

`result.txt` contains the following information for all benchmarks.
- A benchmark file name. (1 line)
- The result of type inference. (1 or 2 lines)
  + If the benchmark is successfully verified, then each line corresponds to a function in the benchmark and consists of
    * "sat" (meaning "satisfied"),
    * the number of CEGIS iterations, and
    * a type of the function inferred by our tool.
  + The timeout is set to 300 seconds.
- Runtime. (1 line)

This should correspond to Table 2 in our paper.
In Table 2, each row contains (1) a benchmark name and (2) runtime if successfully verified within the time limit, and "timeout" otherwise.
Note that runtime may vary depending on the environment.

## Other Tools Mentioned in Our Paper
For those who are interested in comparing our artifact with other tools mentioned in our paper, we provide links to those tools here.
We have provided benchmark files in `benchmarks/OCaml/probabilistic/` that are rewritten for those tools since the input formats for other tools are different from ours.
Note that not all benchmarks can be provided for those tools because our tool and others target slightly different problems.

### [Beutner & Ong, 2021]
Their tool, ASTNAR is available at [https://github.com/ravenbeutner/astnar/tree/main](https://github.com/ravenbeutner/astnar).
We have provided benchmark files in `benchmarks/OCaml/probabilistic/ASTNAR`.

### [Avanzini et al., 2023]
The tool, ev-imp is available at [https://zenodo.org/records/7825902](https://zenodo.org/records/7825902).
We have provided benchmark files in `benchmarks/OCaml/probabilistic/ev-imp`.


## Detailed Documentation for Reusability

### Building the Source Code
See `README.md` at the top directory of the source code.

### Input File Format
These files contain OCaml programs with type annotations for each top-level function.
For example, the type annotation `[@@@assert "typeof(f) <: (x : int) -> { y : int | y = x } "]` means that a function `f` should be of type `(x : int) -> { y : int | y = x }`.

The type of proposition is `prop` and its interpretation should be specified in input files.
- `[@@@mode "hfl_prop_as_expectation"]` means that `prop` is interpreted as a type of non-negative extended real numbers $[0, \infty]$. This mode is used for expected cost analysis, cost moment analysis, and weakest pre-expectation.
- `[@@@mode "hfl_prop_as_conditional_expectation"]` means that `prop` is interpreted as a type of pairs of a non-negative extended real number $[0, \infty]$ and a real number in $[0, 1]$. This mode is used for conditional weakest pre-expectation.

You can find more examples in `benchmarks/OCaml/probabilistic/*.ml`.


### Running the Type Checker

To type check an input file `input.ml`, run the following command:
```bash
dune exec main -- -c ./config/solver/rcaml_pcsat_tb_ar.json -p ml input.ml
```
