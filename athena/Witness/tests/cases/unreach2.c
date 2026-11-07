extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "unreach2.c", 3, "reach_error"); }
extern int __VERIFIER_nondet_int(void);

void check(int v) {
  if (v < 0) { reach_error(); }
}

int main() {
  int x = __VERIFIER_nondet_int();
  if (x > 100) {
    reach_error();
  }
  check(x);
  return 0;
}
