# Notes on these files (written by script/fetch_benchmarks.sh)

**Source.** The C termination benchmarks of the `aeval` repository, `https://github.com/grigoryfedyukovich/aeval`,
branch `term`, directory `c_bench_term/`, at commit `3b1337665b10d3ebb4286e0e8786b28489469d03`. All 171 files are
upstream's bytes except the two below.

**Patched by this repository at fetch time** (`script/fetch/cav2018term.patch`):

- `term_02.c`, `term_03.c` -- upstream declares `int y = __VERIFIER_nondet_int();` twice and never declares `z`,
  which the loop guard (`x > y && y > z` in `term_02.c`, `x > y || y > z` in `term_03.c`) reads, so neither file
  compiles. The patch renames the second declaration to `z`, the evident intent.

The translations of these programs in `benchmarks/LTS/cav2018term/` were made from the patched files.
