// The property is a tautology of LTL: (a U b) || !(a U b), written with R as
// (a U b) || (!a R !b).  Its negation is unsatisfiable, so ltl3ba prints a never
// claim whose only state is `T0_init: false;` -- an automaton with no
// transition, which accepts nothing.  Every run satisfies the property.
// expected: -p cltl valid
//@ ltl invariant a: (AP(x == 0) U AP(x == 1)) || (!AP(x == 0) R !AP(x == 1));
int x = 0;
int main() { while (1) { x = __VERIFIER_nondet_int(); } return 0; }
