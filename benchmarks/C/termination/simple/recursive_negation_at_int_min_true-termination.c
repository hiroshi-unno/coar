/* Terminates: a negative argument is negated once and then counted down to 0.  At INT_MIN the negation
   overflows, which is undefined behaviour; a reading that does not consider an execution past undefined
   behaviour has no execution there either.  The same shape written as a loop
   (while (m < 0) m = -m;) is answered YES under every reading. */
extern int __VERIFIER_nondet_int(void);
int f(int m) { if (m < 0) return f(-m); if (m == 0) return 0; return 1 + f(m - 1); }
int main() { int m = __VERIFIER_nondet_int(); int r = f(m); return 0; }
