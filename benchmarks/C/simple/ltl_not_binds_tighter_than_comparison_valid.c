/* C's `!` binds tighter than a comparison: `!x > 0` is `(!x) > 0`, true exactly
   when x is 0.  Reading it as `!(x > 0)`, that is `x <= 0`, differs at every
   negative x.  Here x is drawn negative before the branch, so the branch is
   never taken and y stays 0; the property's second conjunct holds at every x
   under C's reading and fails at a negative x under the other.  The other
   reading of either occurrence alone makes the answer `invalid`. */
//@ ltl invariant PHI: [] AP(y == 0 && (!(!x > 0) || x == 0));

extern int __VERIFIER_nondet_int();

int x;
int y = 0;

int main() {
    while (1) {
        x = __VERIFIER_nondet_int();
        if (x < 0) {
            if (!x > 0) {
                y = 1;
            }
        }
    }
    return 0;
}
