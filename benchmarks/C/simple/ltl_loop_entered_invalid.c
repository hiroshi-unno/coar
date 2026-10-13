/* The control for the two files beside it: here the guard IS true on entry, the
   body does run, and `i` really can become negative, so `invalid` is the right
   answer.  It pins the direction a repair of the wrong `invalid` must not
   over-shoot into -- dropping the loop guard the other way, or refusing the
   nondeterministic rewrite everywhere, would turn this file `valid`. */
//@ ltl invariant PHI: ([] AP(i >= 0));

extern int __VERIFIER_nondet_int();

int i = 1;
int j;
int main(){
    while ((i - j) >= 1) {
        i = __VERIFIER_nondet_int();
        j = __VERIFIER_nondet_int();
    }
    return 0;
}
