// A backward goto forms a loop: y is incremented until it reaches 3.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 3));
int x = 0; int y = 0;
int main() { L: y = y + 1; if (y < 3) goto L; x = 1; while (1) {} return 0; }
