extern int __VERIFIER_nondet_int(void);
int bound[4];
int main(void) {
  bound[1] = __VERIFIER_nondet_int();
  int a = 0;
  while (a < bound[1]) {   /* bound[1] is not written in the loop */
    a++;
    if (a == 5) return 1;
  }
  return 0;
}
