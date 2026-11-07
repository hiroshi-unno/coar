// The other direction of ltl_continue_in_for_runs_update_valid.c: y ends at 2, never 4.
// Reading continue as a no-op ran y = y + 1 four times and answered valid.
// expected: -p cltl invalid
//@ ltl invariant a: <>(AP(x == 1) && AP(y == 4));
int x = 0; int y = 0; int i = 0;
int main() { for (i = 0; i < 4; i++) { if (i % 2 == 0) continue; y = y + 1; } x = 1; while (1) {} return 0; }
