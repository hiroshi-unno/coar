CAV 2026 Artifact
=======================================
Paper title: Lagrangian-Based Duality for Quantified SMT Algorithms


Claimed badges: Available + Functional + Reusable

Justification for the badges:

  * Functional: The artifact replicates the resuls of the paper (see below for details). It compiles MuCyc and executes the benchmarks on our approach and the tools we compare with. The source code is included in the artifact.
      - replicated: 
          * Figure 1, plot left 
          * Figure 1, plot right   
      
  * Reusable:
      - The artifact's license allows its reuse and repurposing. Source code is provided and the artifact allows several different configuration options. Namely, the benchmarks are evaluated using the approach which satisfies the progress property, as well as an approach where the progress property is not ensured. Moreover, the timeout for the execution of the benchmarks can be adjusted if needed.
      - All dependencies and used libraries are well documented and up to date. Our tool depends on the solver Z3 and the SMT-LIB2 benchmarks. The remaining dependencies are documented in the README file in the root directory of the repository.

Requirements:

  * RAM: 32 GB
  * CPU cores: Single core
  * Time (smoke test): ~1h for setup, max. 300s for single benchmark
  * Time (full review): ´~1h for setup, ~15h to run all the benchmarks

External connectivity: YES

Internet connection is needed to download the SMT-LIB2 benchmark collection.

-------------------------------------------------------------------------------
**                                SETUP                                 **
-------------------------------------------------------------------------------

### Option 1: Loading Docker Image (Recommended)
To load the docker image, run the following command:
```bash
sudo docker load -i mucyc_cav26ae.tar
```
As a final step, benchmarks need to be downloaded (see below).

### Option 2: Building Docker Image
Run the following commands:
```bash
# Unzip the source code
unzip mucyc_cav26ae_src.zip

# Go to the the source code directory
cd mucyc_cav26ae_src

# Build the Docker image
cd cav26ae
sudo docker build -f Dockerfile -t mucyc_cav26ae ../
```
As a final step, benchmarks need to be downloaded (see below).

### Option 3: Manual Setup
See `README.md` in the top directory and follow the instruction to build CoAR. MuCyc is included as part of CoAR.
As a final step, benchmarks need to be downloaded (see below).

### Last step: Download benchmarks
After the setup, the SMT-LIB2 benchmarks need to be downloaded from the link below. The contents of the folder `non-incremental\LRA` (5 directories) need to be copied to `benchmarks/QSMT/LRA`. 

[https://zenodo.org/records/16740866/files/LRA.tar.zst](https://zenodo.org/records/16740866/files/LRA.tar.zst)


-------------------------------------------------------------------------------
**                                SMOKE TEST                                 **
-------------------------------------------------------------------------------

To quickly verify that the setup is working correctly and to demonstrate how to run the experiments, we perform smoke tests on individual benchmarks as described below.

We can run individual benchmarks as follows:

```
timeout=300 ./_build/default/main.exe -c ./config/solver/mucyc_progress_ncr.json -p smt ./benchmarks/QSMT/LRA/2010-Monniaux-QE/mjollnir1/formula_001.smt2
```

The expected output for this particular benchmark is:
```
unsat
```

In general, the output could also be `sat`, `unsat`, `unknown`, or timeout.

The above command executes the approach in which progress property is ensured. Here, `./config/solver/mucyc_progress_ncr.json` can be replaced by `./config/solver/mucyc.json` for executing the approach in which the progress property is not ensured. Similarly, `./config/solver/z3_smt.json` can be used to check the `z3` approach.

Moreover, `2010-Monniaux-QE/mjollnir1/formula_001.smt2` can be replaced with any other benchmark from the benchmark collection set.


-------------------------------------------------------------------------------
**                               FULL REVIEW                                 **
-------------------------------------------------------------------------------

Start a shell inside the container:

```
sudo docker run --rm -it mucyc_cav26ae:latest /bin/bash --login
```

Inside the container, move to the artifact folder and run the LRA experiments:

```
cd /home/opam/coar/cav26ae
./LRA_mucyc.sh > LRA_mucyc.csv
./LRA_mucyc_np.sh > LRA_mucyc_np.csv
./LRA_z3.sh > LRA_z3.csv
```
It will take around 15 hours to run the full set of benchmarks.

Finally, generate the plots:
```
./gen_figs_LRA.sh
```

The following `csv` files are generated: 
- `LRA_mucyc_np.csv`: results of execution time of all benchmarks when using the approach in which progress property is not ensured.
- `LRA_mucyc.csv`: results of execution time of all benchmarks when using the approach in which progress property is ensured.
- `LRA_z3.csv`: results of execution time of all benchmarks when using the SMT solver `z3`.

These files are then used to generate the plots depicted in Figure 1:
- `LRA_mucyc_vs_mucyc_np.pdf`: plot comparing approach with and without progress property
- `LRA_mucyc_vs_z3.pdf`: plot comparing approach with progress property and `z3` solver.
