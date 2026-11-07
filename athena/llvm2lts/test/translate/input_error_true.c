extern int __VERIFIER_nondet_int(void);
extern void __p2a_input_reach_error(void);
int main(void) {
  /* the input's own error event, renamed by Ptr2Arr where reach_error() is
     its marker: the execution ends here, which is no error */
  if (__VERIFIER_nondet_int()) __p2a_input_reach_error();
  return 0;
}
