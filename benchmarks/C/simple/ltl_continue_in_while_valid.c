// A continue in a while loop goes back to the test: z counts the odd values of y
// in 1..4, so it ends at 2.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(z == 2));
int x = 0; int y = 0; int z = 0;
int main() { while (y < 4) { y = y + 1; if (y % 2 == 0) continue; z = z + 1; } x = 1; while (1) {} return 0; }
