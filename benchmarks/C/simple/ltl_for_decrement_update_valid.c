// A for loop counting down with i--: it ends with i == 0.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(i == 0));
int x = 0; int i = 0;
int main() { for (i = 5; i > 0; i--) { } x = 1; while (1) {} return 0; }
