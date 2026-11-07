// The guard's --x runs only while x > 0, so the loop body runs for x = 3, 2
// and 1 and c reaches 3.  Evaluating --x before x > 0 stops it one round
// early.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(c <= 2));
int x = 3;
int c = 0;
int main() {
  while (x > 0 && --x >= 0) { c = c + 1; }
  while (1) {}
  return 0;
}
