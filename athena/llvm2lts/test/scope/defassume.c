extern int __VERIFIER_nondet_int(void);
extern void exit(int);
void __VERIFIER_assume(int b) { if (!b) exit(0); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x > 0);   /* the program's own assume: x <= 0 exits */
  while (x > 0) x--;
  return 0;
}
