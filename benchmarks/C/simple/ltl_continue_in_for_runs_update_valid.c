// A continue in a for loop skips the rest of the body but still runs the update:
// i takes 0..3, the odd ones reach y = y + 1, so y ends at 2 and x = 1 is reached.
// expected: -p cltl valid
//@ ltl invariant a: <>(AP(x == 1) && AP(y == 2));
int x = 0; int y = 0; int i = 0;
int main() { for (i = 0; i < 4; i++) { if (i % 2 == 0) continue; y = y + 1; } x = 1; while (1) {} return 0; }
