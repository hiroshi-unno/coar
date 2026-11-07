# Files for Termination Competition
After creating the Docker image, convert it to an Apptainer image. The Integer Transition Systems category can be solved with MuVal alone, but for the C category, convert .c -> .bc -> .t2 using clang and llvm2kittel before running MuVal.

## Obtaining benchmarks (for testing)
If testing is to be performed afterward, clone the termCOMP benchmark repositories registered as submodules.
```bash
git submodule update benchmarks/term-comp/
git submodule update benchmarks/term-comp-ari/
```

## Creating the Docker image
Build the image for termCOMP based on the image built from the `Dockerfile` at the root of the repository.
```bash
docker build -t coar .
docker build -f script/termcomp/Dockerfile -t termcomp .
```

## Testing the Docker image
When starting the container using `docker compose`, bind mount the directories containing the benchmarks and test scripts used for testing at the same time.

```bash
docker compose -f script/termcomp/compose.yaml up -d
```

Solve the C category benchmarks using llvm2kittel and MuVal.

```bash
docker exec -it termcomp-solver-1 bash -c "script/termcomp/test_llvm2kittel.sh 2> /dev/null"
```

(Example output)

```
output of llvm2kittel (tail):
FROM: main_bb6;
TO: main_bb6_ret;

FROM: main_bb7;
v16 := varg_alloca.0.i - 1;
v17 := varg_alloca1.0.i + 1;
var__temp_varg_alloca.0.i := v16;
var__temp_varg_alloca1.0.i := v17;
TO: main_bb4;

solve using MuVal:
NO
```

## Conversion from a Docker image to an Apptainer image and testing
After converting the image, test the `solver` command.

(Testing contents)

- Check if `solver --name` can be invoked
- Solve one benchmark from the Integer_Transition_Systems category
- Solve one benchmark from the C category

```bash
./script/termcomp/create_apptainer.sh
```

(Example output)

```
INFO:    Starting build...
INFO:    Fetching OCI image...
INFO:    Extracting OCI image...
2025/08/03 17:00:55  warn rootless{root/coar/main.exe} ignoring (usually) harmless EPERM on setxattr "user.rootlesscontainers"
INFO:    Inserting Apptainer configuration...
INFO:    Creating SIF file...
[====================================================================================================================================================================================] 100 % 0s
INFO:    Build complete: <repository-root>/script/termcomp/coar.sif
Test of `solver --name`...
MuVal
Test for Integer_Transition_Systems category...
NO

Test for C category...
YES
```

## Run benchmark test for TermCOMP
- C category
```bash
docker compose -f script/termcomp/compose.yaml up -d
> [+] Running 2/2
> ✔ termcomp:latest                  Built     0.0s
> ✔ Container termcomp-solver-1  Running   0.0s

docker exec -itd termcomp-solver-1 script/termcomp/run_bench_c.sh
```

Benchmark results are written to the following files.

- `termcomp_bench_results/C_muval_"%Y-%m-%d_%H-%M-%S_error.log`: stderr output
- `termcomp_bench_results/C_muval_"%Y-%m-%d_%H-%M-%S.csv`: benchmark results (YES/NO/timeout/abort)
- `termcomp_bench_results/C_muval_"%Y-%m-%d_%H-%M-%S_sorted.csv`: sorted benchmark results
## The rewritten C pipeline (`solver_llvm2lts.sh`)
`solver_llvm2lts.sh` takes the same arguments as `solver.sh` and answers the C categories through the rewritten
pipeline: the new Ptr2Arr (`athena/Ptr2ArrFC`), clang 19.1.7 and llvm2lts (`athena/llvm2lts`), then MuVal with the
same configuration as `solver.sh`, all in one run of CoAR under an Athena configuration the script writes
(`-p cterm`; CoAR built with Frama-C 33 and the LLVM 19 OCaml bindings). `C` and `C_assume` read integers as
mathematical integers, `C_Mod` adds `--wrap-integers` (unsigned arithmetic wraps as in C), and `C_BV` reads every value
as a bit-vector. `C_MemorySafety` is `-p ctermmemsafe`: termination, unless an invalid dereference or free is
reachable (Ptr2Arr `--memory-safety --violation-markers=reach-error --memtrack-check=none`; a leak is not checked),
which gives `MAYBE`. Other categories answer `abort`. The tools are given by `COAR_EXE`, `CLANG19`,
`FRAMAC_SITE_SHARE`, `CONFIG_DIR` and `WORKING_DIR` (the script's head lists the defaults).

```bash
CLANG19=<clang-19> COAR_EXE=$PWD/_build/default/main.exe CONFIG_DIR=$PWD/config WORKING_DIR=$PWD \
  FRAMAC_SITE_SHARE=$(opam var share)/frama-c script/termcomp/solver_llvm2lts.sh --category=C input.c
```
