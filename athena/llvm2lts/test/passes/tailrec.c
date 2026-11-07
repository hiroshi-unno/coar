extern int __VERIFIER_nondet_int(void);
int f(int n) { if (n <= 0) return 0; return f(n - 1); }
int main(void) { return f(__VERIFIER_nondet_int()); }
