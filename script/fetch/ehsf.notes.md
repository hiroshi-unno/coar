# Notes on the E-HSF / ConSynth inputs (written by script/gen_ehsf_echc.py)

**Source.** The `.smt2` files under `benchmarks/{ECHC,pfwnCSP,CHC}/ehsf/` and the `.hes` files under
`benchmarks/muCLP/ehsf/` are translations of the `.qarmc` inputs of E-HSF (Beyene, Popeea and Rybalchenko, *Solving
existentially quantified Horn clauses*, CAV 2013, https://doi.org/10.1007/978-3-642-39799-8_61) and of ConSynth, from
two sources: `consynth/<dir>/` is `tools/consynth/Benchmarks/<dir>/` of `https://github.com/stanlysamuel/gensys`,
branch `gensys-ltl`, commit `1c80c45f34a8462d7e93de68daebec7140d5ee62`; `zip/<dir>/` is the E-HSF archive
`hsf-Benchmarks.zip` (sha256 `f4be99ddc16110f3b6a3ddd7b55b59d9424013e09440721a1dd209a59939bb8d`). Nothing is patched.
`STATUS.tsv` beside this note records every source and the `expected` column it reads from the file name.

**The `-succeed` / `-fail` in a name is the authors' label, not an oracle.** The cases known to be wrong or in doubt,
by `<dir>/<stem>` (a stem may occur in several directories: `ctlstar-cav13`, `ctl/ctlstar-cav13-template`,
`ehsf/cav13/{ext,old,template}` and the archive's copies):

*Wrong for the encoding.*

- `ehsf/cav13/old/25-pimpAF-succeed` -- the clause set is **unsatisfiable**. The C program discards every run with
  `c >= curr_serv` by `assume(c < curr_serv)`, but this encoding puts that guard on the step *out of* the branch
  (`PC=4 -> PC=1`) instead of the step into it, so from `C = CS = 8` the run `PC 1 -> 2 -> 4` enters `PC = 4` and is
  stuck there, which the AF clause counts as a violation. The `ext` version of the same problem places the guard
  correctly.

*Name against the source paper.*

- `28-pimpEF-succeed`, `27-pimpEF-succeed` (`ehsf/cav13/template`), `54-pandEG-succeed`, `56-pandAG-succeed` -- CAV
  2013's Table 1 reports for the Software Updates programs P26-P28 that neither the property nor its negation holds
  (each holds from some initial states only), so over all initial states every file numbered 26-28 or 54-56 is
  unsatisfiable, whatever its suffix. For 28 the C program of the same number (PLDI 2013 industrial program 28,
  Cook and Koskinen, https://doi.org/10.1145/2491956.2491969) fails as well: from `c = 6` its loop is skipped and
  `resp` stays 0.
- `ehsf/cav13/erics/25-EGimpAF-succeed` -- Figure 6 of PLDI 2013 (row 25, `EG(q => AF p)`) expects "fail", and the
  C program embedded in the file is the small benchmark `egimpafp-fail.c`.

*A stale C comment (the name is right).*

- `ehsf/cav13/erics/18-EFEG-fail` and `ehsf/cav13/erics/50-AFEG-fail` -- the C comment in each file is the program
  of `efegp-succeed.c` and `neg-egafp-succeed.c` (PLDI 2013's small benchmarks), but the `init`/`next` clauses encode
  `efegp-fail.c` and `neg-egafp-fail.c`, as each header says (`efegp-fail/original.c`, `neg-egafp-fail/original.c`).
  Both fail at every initial state, as their names and PLDI 2013 Figure 6 rows 18 and 50 say: in 18 every reachable
  state has `p` in {0, -1}, so `EG(p > 0)` holds nowhere; in 50 every path sets `p := 1` within a bounded number of
  steps, so `EG(p <= 0)` holds nowhere. Take the program from the clauses, not from the comment.

*Unresolved (not decided; do not read a verdict from the name).*

- `ehsf/misc/cav15-ltl/toylin1-fail` -- named `fail`, while Cook and Koskinen, *Making prophecies with decision
  predicates*, POPL 2011, https://doi.org/10.1145/1926385.1926431, Table 1, reports that its program (Toy linear
  arith. 1, `c > 5 => F(resp > 5)`) satisfies the property. Not decided from the encoding.

*Headers that do not describe the file.*

- `ehsf/cav13/erics/16-AFAG-fail` and `ehsf/cav13/erics/43-EGEF-succeed` carry a stale copy of the previous file's
  `% No. N` comment (15 and 42). `ctlstar-cav13/Easy/57-simple-robot-sca` and `ctlstar-cav13/Easy/60-cinderella-step`
  carry a header copied from `55-pandAG-fail`; `60-cinderella-step` is also ill-formed (`init` declared with five
  arguments and used with two; `adam`, `eve` undefined).
