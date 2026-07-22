# Files for CHC Competition 2026

## Creating a self-contained zip archive

```bash
# Run from the repository root

# 1. Build the CoAR base image
docker build -t coar:latest .

# 2. Build a image for zip creation
docker build -f script/chccomp2026/createzip.Dockerfile -t coar:chccomp2026-zip .

# 3. Create a self-contained zip archive of CoAR
docker run --rm -v $(pwd)/script/chccomp2026:/output -w /root coar:chccomp2026-zip zip -q -r /output/coar.zip coar

# 4. Build the image for testing the zip archive
docker build -f script/chccomp2026/test_zip.Dockerfile -t coar:chccomp2026-zip-tester .
```

### Running tests with the self-contained zip archive

```bash
# Test before zip compression
docker run --rm -v $(pwd)/benchmarks:/benchmarks coar:chccomp2026-zip ./coar.sh -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp /benchmarks/CHC/simple/sum.smt2

# Test after zip extraction
docker run --rm -v $(pwd)/benchmarks:/benchmarks coar:chccomp2026-zip-tester ./coar.sh -c ./config/solver/dbg_pcsat_tbq_ar.json -p pcsp /benchmarks/CHC/simple/sum.smt2
```
