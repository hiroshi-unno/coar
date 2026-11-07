// U binds tighter than ==>: the property is AP(x == 1) ==> (AP(x == 1) U AP(x == 2)),
// which holds because x is never 1.  Read as (AP(x == 1) ==> AP(x == 1)) U AP(x == 2)
// it would require x to become 2 some time, which it never does.
// expected: -p cltl valid
int x = 0;
//@ ltl invariant a: AP(x == 1) ==> AP(x == 1) U AP(x == 2);
int main() { while (1) {} return 0; }
