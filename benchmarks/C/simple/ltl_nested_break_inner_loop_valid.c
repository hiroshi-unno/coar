// A break leaves only the innermost loop: each of three outer iterations runs
// the inner body twice, so y ends at 6.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 6));
int x = 0; int y = 0; int i; int j;
int main() { i = 0; while (i < 3) { j = 0; while (1) { if (j >= 2) break; j = j + 1; y = y + 1; } i = i + 1; } x = 1; while (1) {} return 0; }
