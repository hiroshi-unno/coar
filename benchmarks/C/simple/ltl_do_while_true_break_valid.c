// do { } while (1); with a break: the loop is left when y reaches 2.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 2));
int x = 0; int y = 0;
int main() { do { y = y + 1; if (y == 2) break; } while (1); x = 1; while (1) {} return 0; }
