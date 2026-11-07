extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = __VERIFIER_nondet_int();
  int j;
  while (i > 0) {
    j = i;
    while (j > 0) {
      j = j - 1;
    }
    i = i - 1;
  }
  return 0;
}
