/* p2a-expect: normal+uninit-check=1 memory-safety+uninit-check=1 assume-safety+uninit-check=1 */
/* A variable-length array: an allocation of its region, outside
   --uninit=check; with --uninit=nondet its elements start nondeterministic
   (written after the allocation). */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int n = (__VERIFIER_nondet_int() & 3) + 2;
    int v[n];
    v[0] = 1;
    return v[0] + v[1];
}
