/* The twin of ltl_not_binds_tighter_than_comparison_valid.c: `!x > 0` is true
   when x is 0, so the branch is taken on a draw of 0 and y becomes 1.  It pins
   the direction a repair must not over-shoot into -- reading `!x` as always 0,
   or dropping the branch, would make this `valid`. */
//@ ltl invariant PHI: [] AP(y == 0);

extern int __VERIFIER_nondet_int();

int x;
int y = 0;

int main() {
    while (1) {
        x = __VERIFIER_nondet_int();
        if (!x > 0) {
            y = 1;
        }
    }
    return 0;
}
