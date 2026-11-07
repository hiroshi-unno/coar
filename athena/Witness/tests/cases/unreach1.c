extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "unreach1.c", 3, "reach_error"); }
extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int i = 0;
  while (i < 10) {
    i++;
  }
  if (x > 5 && i == 10) {
	reach_error();
  }
  return 0;
}
