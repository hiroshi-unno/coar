# Notes on the FSE 2022 termination benchmarks

**Source.** These are translations to T2 transition systems, made by the Athena tool chain in several variants (`C/`,
`C_Mod/`, `C_BV/` with declared bit-vector types, and the top level), of the C programs of Shi, Xie, Li,
Zhang, Chen and Li, *Large-Scale Analysis of Non-Termination Bugs in Real-World OSS Projects*, ESEC/FSE 2022,
https://doi.org/10.1145/3540250.3549129, directory `benchmark/` of
`https://github.com/FSE2022benchmarks/-FSE-2022-Termination` (AGPL-3.0) at commit
`d6fd271e5f0250d4a734678143e9621d8c8aaf4d`. `script/fetch_benchmarks.sh fse2022` places those C programs at
`benchmarks/C/fse2022`.

**The `_T` / `_NT` in a name is the authors' label, not an oracle, and two labels are wrong:**

- `Incorrect_Initialization_2_T` (here `Incorrect_Initialization_2_T.t2`, `C/` and `C_Mod/` of the same name, and
  `C_BV/Incorrect_Initialization_2_T_annotated.t2`) -- **does not terminate**, under integer and bit-vector
  semantics alike. In the C program, start with `matroska != 1` and choose `id == 1` in every inner iteration:
  `res = res_return() < 0` assigns the comparison, so `res` becomes 1 whenever `res_return()` returns a negative
  value, which it may do before `flag` reaches 100 and always does afterwards. The inner loop then exits with
  `res == 1`, `matroska` is unchanged, and the outer loop repeats forever. The authors' own Ultimate Automizer run
  (in the repository's `Evaluation/`) answers `FALSE(TERM)`.
- `Signed_Overflow_Error_1_NT` (here `Signed_Overflow_Error_1_NT.t2`, `C/Signed_Overflow_Error_1_NT.t2` and
  `C_BV/Signed_Overflow_Error_1_NT_annotated.t2`) -- **terminates** in every translation here: the C loop
  `for (i = 1; i <= 0xFFFFFFFF; i <<= 1)` over a `long i` reaches `i = 2^32 > 0xFFFFFFFF` and exits under
  mathematical integers and with a 64-bit `long` (`bv(64)` where a file declares the width). It loops forever only where `long` is
  32 bits. The authors' Ultimate run with `--architecture 64bit` answers `TRUE`.

A run table that reads expected verdicts from these names must override these files.

**One translation disagrees with its program although the label is right:** `C_Mod/Type_Conversion_in_Comparison_2_T.t2`
leaves out the conversion `(unsigned char)c2` in the loop test `ac != (unsigned char)c2`. It compares the wrapped
`unsigned char` counter with the unconverted signed `nondet_char()` value, so `c2 = -1` loops forever in that file,
which is its `_NT` sibling up to renaming. The C program terminates. The top-level and `C_BV/` translations of the same
program keep the conversion. A `NO` for termination on that `C_Mod` file is correct for the file.
