# Notes on these files (written by script/fetch_benchmarks.sh)

**Source.** The LTL benchmarks of Dietsch, Heizmann, Langenfeld and Podelski, *Fairness Modulo Theory: A New Approach
to LTL Software Model Checking*, CAV 2015, https://doi.org/10.1007/978-3-319-21690-4_4, from the Ultimate repository
`https://github.com/ultimate-pa/ultimate` at commit `4636c3456d240cfb917098e460415d4effcbe3ae`:
`trunk/examples/LTL/coolant/` (here `coolant/`), `trunk/examples/LTL/koskinen/ltlcmodelchecker-benchmarks/` (here
`decision-predicates/`; Cook and Koskinen, *Making prophecies with decision predicates*, POPL 2011,
https://doi.org/10.1145/1926385.1926431) and `trunk/examples/LTL/rers2012/` (here `res2012/`). The files are
upstream's bytes except the one below.

**Patched by this repository at fetch time** (`script/fetch/cav2015ltl.patch`):

- `decision-predicates/13-windows_os_frag1.c` -- the line `A = R = 0;` is changed to `a = r = 0;`. Upstream's `A`
  and `R` are declared nowhere; the program's globals are `a` and `r`, which its property
  `[](AP(a != 0) ==> <>AP(r != 0))` reads, so the upstream file is wrong for every tool and the fix is the evident
  intent.
