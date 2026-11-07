// Four nested declarations of a, each shadowing the one outside it.  Each
// inner a is a separate object, so the assignments read the value of the a in
// their own scope: z ends at 2 and w at 3, never 4.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(z != 3) && AP(w != 4));
int z = 0;
int w = 0;
int main() {
  int a = 1;
  if (z == 0) {
    int a = 2;
    if (z == 0) {
      int a = 3;
      if (z == 0) { int a = 4; }
      w = a;
    }
    z = a;
  }
  while (1) {}
  return 0;
}
