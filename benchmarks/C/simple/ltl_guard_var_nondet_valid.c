/* The same defect in its smallest shape: `j` is zero-initialised, read once (in
   the loop guard) and assigned a nondeterministic value in the body, which is
   what made the optimiser treat it as a fresh nondeterministic draw.  The guard
   `j >= 1` is false on entry, so the body never runs and `i` stays 0.
   Answered `invalid` until 2026-07-19. */
//@ ltl invariant PHI: ([] AP(i >= 0));

extern int __VERIFIER_nondet_int();

int i;
int j;
int main(){
    while (j >= 1) {
        i = __VERIFIER_nondet_int();
        j = __VERIFIER_nondet_int();
    }
    return 0;
}
