/* p2a-expect: normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A structure returned by value: none of its fields written when k is 0
   (a violation at the return), one written otherwise (its state is copied
   to the receiver, whose other field is then read: a violation). */
extern int __VERIFIER_nondet_int(void);
struct S { int a; int b; };
struct S mk(int k) {
    struct S r;
    if (k) r.a = 1;
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    return r;
}
int main(void) {
    struct S t;
    __VERIFIER_nondet_int(); /* the first draw of seeds 1-10 is even */
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    t = mk((__VERIFIER_nondet_int() & 1));
    return t.b;
}
