extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 5) __VERIFIER_error();   /* the error event, as reach_error */
  return 0;
}
