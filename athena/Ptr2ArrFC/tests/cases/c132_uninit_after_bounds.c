/* p2a-expect: normal=0 memory-safety=77 assume-safety=0 memory-safety+uninit-check=77 assume-safety+uninit-check=0 */
/* A read out of an array's bounds, of an element never written: in a
   safety mode the bounds violation is reported (valid-deref), not the
   uninitialised read. */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int a[2];
    a[0] = 0;
    int i = 2;
    if (__VERIFIER_nondet_int() == 12345) i = 0;
    if (a[i] == 12345) return 1;
    return 0;
}
