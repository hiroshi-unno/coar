/* Does not terminate, with no overflow on the non-terminating execution: f(1) calls f(-1), which
   calls f(1), for ever.  The negation sits in a recursive call's argument, the position where an
   overflowing negation must stop the path (INT_MIN, recursive_negation_at_int_min_true-termination.c),
   so a reading that stops it must still answer NO here. */
extern int __VERIFIER_nondet_int(void);
int f(int m) { if (m < 0) return f(-m); if (m == 0) return 0; return f(-m); }
int main() { int m = __VERIFIER_nondet_int(); int r = f(m); return 0; }
