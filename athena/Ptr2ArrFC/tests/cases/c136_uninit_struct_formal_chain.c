/* p2a-expect: normal=0 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* The state of a structure passed by value travels through two calls; the
   innermost reads the field nobody wrote (a violation). A call with a
   structure that is not a variable (a global) passes it written. */
extern int __VERIFIER_nondet_int(void);
struct S { int a; int b; };
struct S gs;
int h(struct S v) {
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    return v.b;
}
int f(struct S v) {
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    return h(v);
}
int main(void) {
    struct S s;
    s.a = 1;
    int r = f(gs);
    return r + f(s);
}
