extern int __VERIFIER_nondet_int(void);
int h(int n) { if (n <= 0) return 0; return n + h(n - 1); }
int main(void) { return h(__VERIFIER_nondet_int()); }
