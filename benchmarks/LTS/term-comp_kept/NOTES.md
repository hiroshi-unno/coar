# `LTS/term-comp_kept`: T2 files kept because today's translation refuses their programs

The T2 transition systems of termCOMP's C programs (the TPDB repository, checked out as the `benchmarks/term-comp`
submodule) are generated, not tracked: `script/fetch_benchmarks.sh termcomp-t2` runs `script/gen_termcomp_t2.sh`,
which translates every program of the submodule's `C/` directory with CoAR's own Athena route (the C-to-C rewriting
Ptr2ArrFC on Frama-C, clang 19, `llvm2lts`) under termCOMP's C reading, writes
`benchmarks/LTS/term-comp_llvm2lts/C/<directory>/<name>.t2` with a `MANIFEST.tsv` (CoAR commit, tool versions,
configuration, every program's outcome and checksums), and compares every output with the checksums pinned in
`script/fetch/termcomp-t2.pinned`.

This directory holds the files the repository tracked under `benchmarks/LTS/term-comp/C/` whose programs that
translation refuses or whose generated file is not yet shown to agree (17 on 2026-11-03, 5 since 2026-11-04), at
the same relative paths and under the same names. They were written in 2025 by an earlier
version of the same pipeline (a clang-based pointer-to-array rewrite, LLVM's `tailcallelim`, then `llvm2lts`), which
turned some recursion into loops and read some constructs the current route declines; nothing regenerates them.

## Why each is kept

| file (under `C/`) | why it is kept |
| --- | --- |
| `AProVE_memory_unsafe/svcomp_delete_alloca_unsafe.t2` | outside the rewriting's fragment (Ptr2ArrFC declines it) |
| `AProVE_memory_unsafe/svcomp_delete_unsafe.t2` | the rewriting (Ptr2ArrFC) fails on it (status 1) |
| `SV-COMP_Mixed_Categories/BallRajamani-SPIN2000-Fig1_false-unreach-call.t2` | llvm2lts fails with `Failure("Not an instruction")` |
| `SV-COMP_Mixed_Categories/rekcba_aso_false-unreach-call.1.M1.t2` | a call of a function without a body (`ecrobot_bt_data_logger`) |
| `SV-COMP_Mixed_Categories/rekcba_nxt_false-unreach-call.1.M1.t2` | a call of a function without a body (`ecrobot_status_monitor`) |

**Twelve files left this set on 2026-11-04** (Binomial_true and rec_strlen at the maintainer's word: their programs are generated now, so a kept copy only duplicates an input; both copies were undecided at 300 s, so agreement is unshown)

**Ten of them left**, when the generator's configuration gained the accumulator form of tail
recursion and simplifycfg (`tail_recursion: Accumulated`, `control_flow: Simplified`; athena/docs/llvm2lts-spec.md
§ 7.6) and translated their programs; each generated file gave this file's answer in every one of five runs
(`muval.json -p ltsterm`, 60 s): `AProVE_numeric/{Avg_true, LogRecursive_true, TerminatorRec02_true, TwoWay_true,
svcomp_MultCommutative_true-unreach-call_true-termination_modified, Et4_true}` and
`SV-COMP_Mixed_Categories/{id_i10_o10_false-unreach-call, cdaudio_simpl1_false-unreach-call_true-termination.cil,
diskperf_simpl1_true-unreach-call_true-termination.cil}` YES, `Ultimate/RecursiveNonterminating_false-termination` NO.
(The first six and `id_i10_o10` had been refused for recursion other than a tail call; `Et4_true` and
`RecursiveNonterminating` for the empty block the rewriting's single return point leaves before a `void` function's
return; `cdaudio` and `diskperf` for "an undef operand", in fact the `poison` that `mem2reg` puts on a phi input from an
unreachable block, which simplifycfg removes.) `git checkout 80fa2a1c1c -- benchmarks/LTS/term-comp_kept` restores them.

**The recursive programs are answered from C.** Athena's direct route translates LLVM IR to a fixpoint problem with
one predicate per function, so it keeps calls as calls and does not refuse recursion:

    ./_build/default/main.exe -c ./config/solver/athena_direct_unbounded.json -p cterm \
        benchmarks/term-comp/C/<directory>/<name>.c

(`athena_direct_unbounded.json` is termCOMP's C reading on that route.)

**`rekcba_nxt_false-unreach-call.1.M1.t2` is ill-sorted under the bit-vector reading**: it feeds the result of a
`real2int` to `ubv2real(32, _)`, which CoAR refuses under `-p ltstermbv`; under `-p ltsterm` it reads.

## The rest of `benchmarks/LTS/term-comp`, removed on 2026-11-03

Every other T2 file under `benchmarks/LTS/term-comp/` was deleted on 2026-11-03:

- `C/`: the 717 files the generator now writes from the same programs. Their tracked versions came from the 2025
  pipeline (and a regeneration of 2026-06-07); on a 40-program sample the generated files gave the tracked files'
  answer wherever both decided and never contradicted a verdict in a file name, and four of them -- the
  two-dimensional arrays of `Di_Stefano_20/{boids,flock,formation,majority}_true-termination` -- are now well-sorted,
  where the tracked files wrote one array once with arrays and once with integers as its elements.
- `C_Integer/Stroeder_15_t2/` and `C_Integer/Ton_Chanh_15_t2/` (316 + 19 files): llvm2kittel translations of 2020-2021
  of programs that are byte-identical copies of `C/Stroeder_15/` and of 19 of `C/Ton_Chanh_15/`, which the generator
  translates.
- `C_Integer/Stroeder_15_t2_hkhlaaf/`, `Stroeder_15_t2_s-falke/`, `Ton_Chanh_15_t2_hkhlaaf/`, `Ton_Chanh_15_t2_s-falke/`
  (316 + 316 + 19 + 19 files): the output of llvm2kittel variants with known defects (one places an edge's copies
  before the branch that chooses the edge, so `Stroeder_15_t2_hkhlaaf/gcd1_true-termination.t2` does not terminate
  although its program does), deleted outright.

Restore any of them with

    git checkout 8653375e9421fcf1df59b5e1d514c96d587b5df5 -- benchmarks/LTS/term-comp

(`8653375e9421fcf1df59b5e1d514c96d587b5df5` is the last commit holding all of them.)

## 36 empty files removed earlier (2026-11-03)

Before the files above went, 36 files of `C/` were removed because they were **0 bytes from their first commit**
(`d87587d010`, 2025-07-01). They are not lost conversions: every one of the 36 programs is recursive, and `llvm2lts`
refuses recursion other than a tail call, so the pipeline produced nothing for them; the generator refuses them too.
An empty transition system is decided vacuously, so the files only gave answers that contradicted their names.
`git checkout 0716f5cc69 -- benchmarks/LTS/term-comp/C/<directory>/<name>.t2` restores any of them (`0716f5cc69` is the
last commit holding them; any earlier commit back to `d87587d010` holds the same empty files). Their C sources are
answered through the direct route as above, for example `benchmarks/term-comp/C/AProVE_numeric/ex2.c` for the removed
`AProVE_numeric/ex2.t2`.

Removed files (paths under `benchmarks/LTS/term-comp/C/`):

- `AProVE_numeric/Parts_true.t2`
- `AProVE_numeric/ex2.t2`
- `AProVE_numeric/ex3.t2`
- `AProVE_numeric/rec_counter1.t2`
- `AProVE_numeric/rec_counter3.t2`
- `AProVE_numeric/svcomp_Ackermann01_true-unreach-call_modified_modified.t2`
- `AProVE_numeric/svcomp_EvenOdd01_true-unreach-call_true-termination_modified.t2`
- `AProVE_numeric/svcomp_Fibonacci01_true-unreach-call_modified.t2`
- `AProVE_numeric/svcomp_recHanoi02_true-unreach-call_true-termination_modified.t2`
- `Hensel_22/nondet_ll_init_rec.t2`
- `Hensel_22/nondet_ll_traverse_rec.t2`
- `SV-COMP_Mixed_Categories/EvenOdd01_true-unreach-call_true-termination.t2`
- `SV-COMP_Mixed_Categories/Fibonacci01_true-unreach-call.t2`
- `SV-COMP_Mixed_Categories/McCarthy91_false-unreach-call_false-termination.t2`
- `SV-COMP_Mixed_Categories/Primes_true-unreach-call.t2`
- `SV-COMP_Mixed_Categories/afterrec_2calls_false-unreach-call.t2`
- `SV-COMP_Mixed_Categories/fibo_2calls_2_false-unreach-call.t2`
- `SV-COMP_Mixed_Categories/fibo_5_false-unreach-call.t2`
- `SV-COMP_Mixed_Categories/id2_b2_o3_true-unreach-call.t2`
- `SV-COMP_Mixed_Categories/recHanoi01_true-unreach-call_true-termination.t2`
- `SV-COMP_Termination_Category/LeeJonesBen-Amram-POPL2001-Ex2_true-termination.t2`
- `SV-COMP_Termination_Category/LeeJonesBen-Amram-POPL2001-Ex3_true-termination.t2`
- `SV-COMP_Termination_Category/joey_false-termination.t2`
- `Ton_Chanh_15/Ackermann_false-termination.t2`
- `Ton_Chanh_15/Ackermann_true-termination.t2`
- `Ton_Chanh_15/McCarthy91_Recursion_true-termination.t2`
- `Ton_Chanh_15/MutualRecursion_1a_false-termination.t2`
- `Ton_Chanh_15/MutualRecursion_1b_true-termination.t2`
- `Ton_Chanh_15/NestedRecursion_1a_false-termination.t2`
- `Ton_Chanh_15/NestedRecursion_1b_true-termination.t2`
- `Ton_Chanh_15/NestedRecursion_1c_true-termination.t2`
- `Ton_Chanh_15/NestedRecursion_1d_true-termination.t2`
- `Ton_Chanh_15/NestedRecursion_2a_false-termination.t2`
- `Ton_Chanh_15/NestedRecursion_2b_false-termination.t2`
- `Ton_Chanh_15/NestedRecursion_2c_true-termination.t2`
- `Ultimate/RecursiveMultiplication_true-termination.t2`
