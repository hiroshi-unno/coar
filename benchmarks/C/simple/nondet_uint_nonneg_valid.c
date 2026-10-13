// __VERIFIER_nondet_uint() gives x >= 0 (32-bit types keep
// the historical treatment: no upper bound), so x >= 0 holds. expected: -p cltl valid
//@ ltl invariant a: [](AP(x >= 0));
extern unsigned int __VERIFIER_nondet_uint();
int x;
int main() {
  x = __VERIFIER_nondet_uint();
  while (1) {}
  return 0;
}
