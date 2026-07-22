# Files for CHC Competition 2025

## Obtaining benchmarks (for testing)
If testing is to be performed afterward, clone the CHC COMP benchmark repositories that are registered as submodules.
```bash
git submodule update benchmarks/chc-comp25
```

## Creating the Docker image
Build the CoAR Docker image using the `Dockerfile` at the root of the repository.
```bash
docker build -t coar .
```


## Run benchmark test for chccomp
When starting the container using `docker compose`, bind mount the directories containing the benchmarks and the scripts for running PCSat/MuCyc on them at the same time.

```bash
docker compose -f script/chccomp2025/compose.yaml up -d
> [+] up 2/2
> ✔ Network chccomp2025_default    Created    0.0s
> ✔ Container chccomp2025-solver-1 Started    0.1s

# PCSat
docker exec -itd -w /root/coar chccomp2025-solver-1 "script/chccomp2025/run_bench_pcsat.sh"

# MuCyc
docker exec -itd -w /root/coar chccomp2025-solver-1 "script/chccomp2025/run_bench_mucyc.sh"
```

Benchmark results are written under `script/chccomp2025/bench_results/`.

- `<solver>_"%Y-%m-%d_%H-%M-%S/<track>_"%Y-%m-%d_%H-%M-%S_error.log`: stderr output
- `<solver>_"%Y-%m-%d_%H-%M-%S/<track>_"%Y-%m-%d_%H-%M-%S.csv`: benchmark results (YES/NO/timeout/abort)
- `<solver>_"%Y-%m-%d_%H-%M-%S/<track>_"%Y-%m-%d_%H-%M-%S_sorted.csv`: sorted benchmark results