// A bool draw used as a condition (rather than assigned) is 0 or 1.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x <= 1));
extern int __VERIFIER_nondet_bool();
int x = 0;
int main() { if (__VERIFIER_nondet_bool()) { x = 1; } while (1) {} return 0; }
