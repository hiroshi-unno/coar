// A default placed before other cases: c + 1 == 8 matches no case, so control
// enters at default and falls into case 2, y = 10 + 3.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 13));
int x = 0; int y = 0; int c = 7;
int main() { switch (c + 1) { case 0: y = 1; break; default: y = 10; case 2: y = y + 3; break; case -1: y = 4; } x = 1; while (1) {} return 0; }
