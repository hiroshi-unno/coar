// A continue in do { } while (1) goes to the test, here always true: y is
// incremented until it reaches 3, then break leaves the loop.
// expected: -p cltl valid
//@ ltl invariant a: <>(AP(x == 1) && AP(y == 3));
int x = 0; int y = 0;
int main() { do { y = y + 1; if (y < 3) continue; break; } while (1); x = 1; while (1) {} return 0; }
