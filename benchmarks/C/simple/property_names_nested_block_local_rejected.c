// The property names j, a local of a block nested in main: it is no single
// variable of the whole run (it exists only while the block runs), so the file
// is refused.  The block redeclares nothing, which is the case where its
// statements are not kept apart from main's own.
// expected: -p cltl refused ("neither a global variable nor a local declared in main's outermost block")
//@ ltl invariant a: [](AP(j == 0));
int main() {
  int i = 0;
  { int j = 0; }
  while (1) {}
  return 0;
}
