extern unsigned int __VERIFIER_nondet_uint(void);
int main(void) {
  unsigned int x = __VERIFIER_nondet_uint();
  if (x % 2 == 1) {
    while (x != 0) {
      x = x + 2;
    }
  }
  return 0;
}
