/* Does not terminate: the negation is done in unsigned arithmetic, which wraps without undefined
   behaviour, so at INT_MIN it gives 2^31, which converts back to INT_MIN (the conversion is
   implementation-defined; gcc and clang keep the low bits), and f(INT_MIN) calls itself for ever.
   The reading that makes every wrap-around explicit (Athena's C_Mod, athena_direct_mod.json) must
   answer NO; a reading with no wrap-around may answer either way.  Sibling of
   recursive_negation_at_int_min_true-termination.c, whose negation is signed and so undefined there. */
extern int __VERIFIER_nondet_int(void);
int f(int m) { if (m < 0) return f((int)(0u - (unsigned)m)); if (m == 0) return 0; return 1 + f(m - 1); }
int main() { int m = __VERIFIER_nondet_int(); int r = f(m); return 0; }
