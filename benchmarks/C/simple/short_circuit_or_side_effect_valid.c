// The right operand of || is evaluated only when the left one is false, and of
// && only when the left one is true.  x is 0 throughout, so neither --x runs.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x >= 0));
int x = 0;
int main() {
  if (x == 0 || --x == 5) { }
  if (x != 0 && --x == 5) { }
  while (1) {}
  return 0;
}
