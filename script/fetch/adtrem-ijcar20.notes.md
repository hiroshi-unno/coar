# Notes on these files (written by script/fetch_benchmarks.sh)

**Source.** The benchmark archive of De Angelis, Fioravanti, Pettorossi and Proietti, *Removing Algebraic Data Types
from Constrained Horn Clauses Using Difference Predicates*, IJCAR 2020, https://doi.org/10.1007/978-3-030-51074-9_6,
served at `https://fmlab.unich.it/adtrem/adtrem-ijcar20/ADTRem-benchmarks.tgz` (sha256
`6fb3630b6c980a90ec9f5c6d75fe65f368c81a35dfd212a2f39fce54f2ba676c`). Every file outside `length-lemma/` is upstream's
bytes, unpatched.

**Added by this repository, not upstream's:**

- `length-lemma/adtrem_clam_goal2_length_lemma_sat.smt2`, `length-lemma/adtrem_clam_goal4_length_lemma_sat.smt2` --
  copies of `CHC-source/clam/goal2.smt2` and `goal4.smt2` to which `script/fetch/adtrem-ijcar20.patch` adds eight
  lines: a recursive `length` function on `listOfInt` and a `set-info` hint that `length` is positive on a non-empty
  list. The hint is a claim a solver must prove before using it; the problems are otherwise the originals.
