// A switch with no default and no matching case runs none of its body.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 0));
int x = 0; int y = 0; int c = 5;
int main() { switch (c) { case 0: y = 1; break; case 1: y = 2; } x = 1; while (1) {} return 0; }
