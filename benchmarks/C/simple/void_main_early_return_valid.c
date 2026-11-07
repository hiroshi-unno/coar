// A bare return from a void main ends the run before x = 1.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 0));
int x = 0;
void main() { if (x == 0) { return; } x = 1; while (1) {} }
