// Probes the TODO(bug) in lib/c/optimizer.ml's RemoveAssign (the `Once` case):
// "check whether any path from assign stmt to stmt using the assigned var don't pass an
// assignment".  Here the nondet assignment to y is overwritten by y = 5 before the use, so
// removing it and substituting the nondet into `x = y` would be wrong.  The [can_remove] test
// demands one reaching assignment, which blocks that.  Expected: valid (x = 5 < 1000).
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x;
int y = __VERIFIER_nondet_char();
int main() { y = 5; x = y; while (1) {} return 0; }
