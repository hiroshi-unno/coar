/* The source map of the record on a switch: the switch is not a branch
   (only selection by if and the loops are); the statements under the case
   labels are placed after their labels, and the input's reach_error under a
   case label is an unreach-call target. */
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
int g;
int main(void) {
  int s = __VERIFIER_nondet_int();
  switch (s) {
  case 1: g = 1; break;
  case 2: reach_error();
  default: g = 3;
  }
  return g;
}
