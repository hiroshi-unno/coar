extern void reach_error(void);
extern unsigned int __VERIFIER_nondet_uint(void);

int main(void) {
  unsigned int n = __VERIFIER_nondet_uint();
  int i = 0;
  while (i < 100) {
    i++;
  }
  if (i != 100) reach_error();
  return n - n;
}
