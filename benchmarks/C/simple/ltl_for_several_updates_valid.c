// A for loop with two initialisations and two updates, run in order: three
// iterations, so j ends at 6.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(j == 6));
int x = 0; int i = 0; int j = 0;
int main() { for (i = 0, j = 0; i < 3; i++, j = j + 2) { } x = 1; while (1) {} return 0; }
