// The property names i, a local declared in main's outermost block, which has
// a value in every state of the run; it means that variable.  main never
// changes i, so the property holds.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(i == 0));
int main() { int i = 0; while (1) {} return 0; }
