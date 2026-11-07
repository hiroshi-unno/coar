extern int __VERIFIER_nondet_int(void);
int main(void) {
  int s = 0;
  for (int i = 0; i < 3; i++) {
    int x;
    if (__VERIFIER_nondet_int()) x = 1;
    s += x;
  }
  return s;
}
