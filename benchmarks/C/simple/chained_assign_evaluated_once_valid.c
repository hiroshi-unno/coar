// x = y = x + 1 is x = (y = x + 1): the right-hand side is evaluated once,
// before x changes, so both end at 1 and x never exceeds y.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x <= y));
int x = 0;
int y = 0;
int main() { x = y = x + 1; while (1) {} return 0; }
