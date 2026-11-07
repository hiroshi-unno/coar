extern int __VERIFIER_nondet_int(void);
int one(void) { return 1; }
int two(void) { return 2; }
int main(void) { int (*p)(void) = __VERIFIER_nondet_int() ? one : two; return p(); }
