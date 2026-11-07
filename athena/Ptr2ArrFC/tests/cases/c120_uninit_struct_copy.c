/* p2a-expect: normal+uninit-check=1 memory-safety+uninit-check=1 assume-safety+uninit-check=1 */
/* A structure with one field written is copied whole (not a violation),
   then the copy's unwritten field is read on some seeds (a violation). */
extern int __VERIFIER_nondet_int(void);
struct S { int a; int b; };
int main(void) {
    struct S s, t;
    s.a = 1;
    __VERIFIER_nondet_int(); /* the first draw of seeds 1-10 is even */
    t = s;
    __VERIFIER_nondet_int(); /* marks the position in the trace */
    int r = t.a;
    if ((__VERIFIER_nondet_int() & 1)) r += t.b;
    return r;
}
