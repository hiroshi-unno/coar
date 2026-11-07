# Notes on these files (written by script/fetch_benchmarks.sh)

**Source.** 180 crafted- and random-track instances of SAT Competition 2016, downloaded one by one from the Global
Benchmark Database (`https://benchmark-database.de`) by their GBD instance hash, which names the clause content;
the hash of each file is in `script/fetch/sc2016-gbd.manifest`. The competition's own archives are no longer served.

**Patched by this repository at fetch time** (`script/fetch/sc2016-gbd.patch`): GBD serves the clauses without
comment lines. The patch puts back the generators' comment headers of 132 files (the `fla-` seeds and planted
solutions, the `unif-k5` generator line, the `c Reshuffling of:` headers) and the trailing blank line of 58 `fla-`
files, as they were in the copy this repository held before. The clauses, and so every answer, are GBD's unchanged.
