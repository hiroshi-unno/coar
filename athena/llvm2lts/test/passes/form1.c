extern int __VERIFIER_nondet_int(void);
int g(int n, int d) {
  if (n <= 0) return 0;
  int r = g(n - 1, d);
  int unused = 100 / d;
  return r;
}
int main(void) { return g(__VERIFIER_nondet_int(), __VERIFIER_nondet_int()); }
