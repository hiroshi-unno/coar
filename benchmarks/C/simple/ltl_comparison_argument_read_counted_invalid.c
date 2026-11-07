/* The twin of ltl_comparison_argument_read_counted_valid.c with the draw read
   only inside the comparison passed to g: that read is the draw's only one, so
   the draw must survive, and a positive x makes z 1.  Counting no read there
   removed the draw and crashed with x unbound. */
//@ ltl invariant PHI: [] AP(z == 0);

extern int __VERIFIER_nondet_int();

int x;
int z = 0;

int g(int b) {
    return b;
}

int main() {
    while (1) {
        x = __VERIFIER_nondet_int();
        z = g(x > 0);
    }
    return 0;
}
