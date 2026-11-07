/* `g(x > 0)` passes the comparison's value, which the frontend writes as
   `ite(x > 0, 1, 0)`, and the x it reads is a read of the drawn value like any
   other.  When the optimiser did not count reads inside that condition, the
   draw looked read once (by `x < 0`), the branch became a free choice, the
   draw was removed, and the read in the argument was left with x unbound: a
   crash.  Here x is negative whenever g is called, so g returns 0 and y
   stays 0. */
//@ ltl invariant PHI: [] AP(y == 0);

extern int __VERIFIER_nondet_int();

int x;
int y = 0;

int g(int b) {
    return b;
}

int main() {
    while (1) {
        x = __VERIFIER_nondet_int();
        if (x < 0) {
            if (g(x > 0) == 1) {
                y = 1;
            }
        }
    }
    return 0;
}
