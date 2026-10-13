/* Both globals are zero-initialised, so the loop guard `i - j >= 1` is false on
   entry and the body never runs: `i` keeps its initial 0 and the property holds.
   The optimiser used to eliminate `j` as a value read once nondeterministically,
   and the state update that would have carried `j = 0` into the query was
   silently discarded because `j` was no longer in the state -- the guard then
   mentioned a variable the query predicate did not carry, both successors of the
   `while` were taken unconditionally, and `i` became an arbitrary integer.
   Answered `invalid` until 2026-07-19.  The property must name only `i`: a
   variable that occurs in the LTL formula is excluded from the read graph and so
   from the rewrite, which is why naming `j` in the property hid this. */
//@ ltl invariant PHI: ([] AP(i >= 0));

extern int __VERIFIER_nondet_int();

int i;
int j;
int main(){
    while ((i - j) >= 1) {
        i = __VERIFIER_nondet_int();
        j = __VERIFIER_nondet_int();
    }
    return 0;
}
