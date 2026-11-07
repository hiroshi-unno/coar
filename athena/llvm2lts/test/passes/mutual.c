extern int __VERIFIER_nondet_int(void);
int odd(int n);
int even(int n) { if (n == 0) return 1; return odd(n - 1); }
int odd(int n) { if (n == 0) return 0; return even(n - 1); }
int main(void) { return even(__VERIFIER_nondet_int()); }
