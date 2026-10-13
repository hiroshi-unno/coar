// The range of __VERIFIER_nondet_char() must also apply when the call is an
// initialiser (a rule that once covered only the assignment form). expected: -p cltl valid
//@ ltl invariant a: [](AP(x < 1000));
extern char __VERIFIER_nondet_char();
int x = __VERIFIER_nondet_char();
int main() { while (1) {} return 0; }
