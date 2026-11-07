// The other direction of void_main_early_return_valid.c: the return is not
// taken, so x = 1 runs.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x == 0));
int x = 0;
void main() { if (x != 0) { return; } x = 1; while (1) {} }
