// The property names i, a local declared in main's outermost block (after a
// bare block declaring a local of its own), and means that variable: main sets
// it to 1 inside the loop, so the property fails.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(i == 0));
int main() {
  { int j = 0; }
  int i = 0;
  while (1) { i = 1; }
  return 0;
}
