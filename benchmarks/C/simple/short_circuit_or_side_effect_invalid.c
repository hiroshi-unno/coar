// The other direction of short_circuit_or_side_effect_valid.c: here the left
// operand of || is false, so --x runs and x becomes 0.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x >= 1));
int x = 1;
int main() {
  if (x == 0 || --x == 5) { }
  while (1) {}
  return 0;
}
