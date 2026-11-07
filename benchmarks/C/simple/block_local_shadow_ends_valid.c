// A declaration in a bare block shadows the outer a only until the block
// ends, so z = a reads the outer a, 1.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(z != 2));
int z = 0;
int main() {
  int a = 1;
  { int a = 2; }
  z = a;
  while (1) {}
  return 0;
}
