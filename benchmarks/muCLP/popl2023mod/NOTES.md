# Notes on third-party programs in this corpus

Most files here are this repository's own muCLP encodings. Two groups encode other authors' benchmarks, and a user of
them should know the following. The encodings are kept as generated and are not edited here.

## `pldi2013_industrial_*`, `pldi2013_small_*`: PLDI 2013 CTL benchmarks

Encodings of the CTL benchmarks of Byron Cook and Eric Koskinen, *Reasoning about nondeterminism in programs*,
PLDI 2013, https://doi.org/10.1145/2491956.2491969; each `.c` here is a byte-identical copy of
`benchmarks/C/pldi2013ctl/<industrial|small>/<name>.c`, and its `.hes` states that the CTL property holds at every
initial state (the top formula quantifies the nondeterministic initial values universally). The `-succeed` / `-fail`
suffix is the original authors' label, not an oracle:

- `pldi2013_industrial_28-pimpEF-succeed.c{,.hes}` -- **the property fails** (`invalid`), so the name is wrong.
  The property is `c <= 5 \/ EF(resp > 5)`; the program runs its loop only when `c <= 5`, so from the initial state
  `c = 6` the loop is skipped, `resp` stays 0, and both disjuncts are false.
- `pldi2013_industrial_12-AGimpEF-succeed` (holds), `pldi2013_industrial_27-pimpEF-fail` (fails) and
  `pldi2013_industrial_40-EFandAG-fail` (fails) -- the names give the verdict of the program, but the paper's
  Figure 7 states the opposite expected result for rows 12, 27 and 40. The programs here, not the names, are what
  differ from the paper: 12 and 40 are a version of OS fragment 3 whose last loop can always exit into `keR = 1`
  (40's property is the negation of 12's), and 27 has `servers = 4`, so `resp` never exceeds 4 and `EF(resp > 5)`
  fails from `c = 6`.

`benchmarks/C/pldi2013ctl/NOTES.md` gives the argument for each.

## `cav2015ltl-hes/`: CAV 2015 LTL benchmarks

Encodings of the `coolant/` and `decision-predicates/` programs of the LTL benchmarks of Dietsch, Heizmann,
Langenfeld and Podelski, *Fairness Modulo Theory: A New Approach to LTL Software Model Checking*, CAV 2015, https://doi.org/10.1007/978-3-319-21690-4_4 (the
programs are in `github.com/ultimate-pa/ultimate`, `trunk/examples/LTL/`; the decision-predicates set is Cook and
Koskinen's, *Making prophecies with decision predicates*, POPL 2011,
https://doi.org/10.1145/1926385.1926431). They were generated from the authors' 2015 benchmark archive with one local fix:

- `decision-predicates/13-windows_os_frag1.c.hes` -- encodes the program with `a = r = 0;` where the original
  writes `A = R = 0;`. The original's `A` and `R` are declared nowhere; its globals are `a` and `r`, which its property
  `[](AP(a != 0) ==> <>AP(r != 0))` reads, so the original does not compile and the fix is the evident intent.
  The same fix is applied when `benchmarks/C/cav2015ltl` is fetched.

## The pldi2013 files and the 2026-11-02 CTL-frontend repairs

These files are kept as generated and are not regenerated: each is a well-defined muCLP problem whose answer is fixed by
the file itself, and published results were measured on them. What changed is how they relate to the C programs in
`benchmarks/C/pldi2013ctl` they were generated from. Since 2026-11-02 the C frontend reads a CTL property as holding at
every initial state, whatever its outermost operator; before, a property whose outermost operator is `E` was asked of
some initial state. Printing all 117 C files with the frontend before and after the repairs (`printer.json -p cctl`)
changes 26 translations, each of which has its copy here:

- 25 change only the top-level binder of the initial values, `exists` -> `forall`: `pldi2013_industrial_33-EFandEG-fail.c.hes`, `pldi2013_industrial_34-EFandEG-succeed.c.hes`, `pldi2013_industrial_35-EFandAG-fail.c.hes`, `pldi2013_industrial_36-EFandAG-succeed.c.hes`, `pldi2013_industrial_45-EFEG-fail.c.hes`, `pldi2013_industrial_46-EFEG-succeed.c.hes`, `pldi2013_industrial_47-EFAG-fail.c.hes`, `pldi2013_industrial_48-EFAG-succeed.c.hes`, `pldi2013_industrial_49-EFEG-fail.c.hes`, `pldi2013_industrial_50-EFEG-succeed.c.hes`, `pldi2013_industrial_51-EFAG-fail.c.hes`, `pldi2013_industrial_52-EFAG-succeed.c.hes`, `pldi2013_small_efafp-succeed.c.hes`, `pldi2013_small_efegp-fail.c.hes`, `pldi2013_small_efegp-succeed.c.hes`, `pldi2013_small_egefp-fail.c.hes`, `pldi2013_small_egefp-succeed.c.hes`, `pldi2013_small_egimpefp-succeed.c.hes`, `pldi2013_small_neg-afagp-fail.c.hes`, `pldi2013_small_neg-afagp-succeed.c.hes`, `pldi2013_small_neg-afp-fail.c.hes`, `pldi2013_small_neg-afp-succeed.c.hes`, `pldi2013_small_neg-agafp-fail.c.hes`, `pldi2013_small_neg-agafp-succeed.c.hes`, `pldi2013_small_neg-agimpefp-fail.c.hes`. Their verdict as C programs
  changes for three of them (`pldi2013_industrial_50-EFEG-succeed.c.hes`, `pldi2013_industrial_52-EFAG-succeed.c.hes`,
  `pldi2013_small_neg-agafp-succeed.c.hes`: valid here, invalid for the C program); for the other 22 the two readings
  give the same answer. These files therefore state "for some initial state" of an `E` property.
- `pldi2013_small_afp-succeed.c.hes` changes in its body: `!y > 0` is now C's `(!y) > 0` (that is, `y == 0`), where this
  file has `not (y > 0)`; its verdict is the same either way.

A corrected set, if one is wanted, is generated under new names; these files stay as they are.

## The cav2015ltl-hes files and the 2026-11-02 C-LTL repairs

Also kept as generated. The 41 C programs (`script/fetch_benchmarks.sh cav2015ltl`, Ultimate commit `4636c345`) were
printed with `printer.json -p cltl` by three builds: one with the C frontend repairs of 2026-11-02 but before the
LTL-to-Büchi repairs, one just before those (parenthesised formula handed to ltl3ba, empty never claim, transition-less
state), and one after them. The first two print all 41 identically; the last changes four, `04-toylinarith1`,
`05-toylinarith2`, `09-postgreSQL_dropbuf_prop1` and `11-apache_accept_liveness` (a different Büchi automaton, so
different state names and equations). MuVal answers the before and after prints of each of the four alike
(`invalid`, `valid`, `invalid`, `invalid`), the same as these files. `13-windows_os_frag1` is refused by all three builds
(`56:8: syntax error`; upstream initialises `A` and `R`, which the fetch script patches to `a` and `r`, and the census
read the unpatched file). Not covered: the C frontend repairs before those (inlined parameters and the other findings
of that batch), for want of a build older than them; their effect on these files is not measured.
