// C integers are mathematical integers in this frontend; unsigned wrap-around
// is not modelled, only warned about ([warning] `unsigned` ... under -v).
// expected: -p cltl invalid (C semantics would make it valid)
//@ ltl invariant a: [](AP(x >= 0));
unsigned int x = 0;
int main() { x = x - 1; while (1) {} return 0; }
