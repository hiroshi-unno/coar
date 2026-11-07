/* p2a-expect: normal=0 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A structure with one field written is passed by value (not a violation);
   the callee reads the field the caller did not write (a violation). */
extern int __VERIFIER_nondet_int(void);
struct S { int a; int b; };
int f(struct S v) {
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    return v.a;
}
int main(void) {
    struct S s;
    s.b = 1;
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    return f(s);
}
