/* main written as the SV-COMP tasks from Linux drivers write it. */
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
void main(void) {
  int x = __VERIFIER_nondet_int();
  if (x == 3) reach_error();
}
