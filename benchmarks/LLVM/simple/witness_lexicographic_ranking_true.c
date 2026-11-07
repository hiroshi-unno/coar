extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  while (i > 0) {
    if (j > 0) {
      j = j - 1;
    } else {
      i = i - 1;
      j = __VERIFIER_nondet_int();
    }
  }
  return 0;
}
