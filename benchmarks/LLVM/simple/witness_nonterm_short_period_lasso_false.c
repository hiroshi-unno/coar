extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = 0;
  int k = __VERIFIER_nondet_int();
  while (k > 0) {
    i = i + 1;
    if (i == 4) {
      i = 0;
    }
  }
  return 0;
}
