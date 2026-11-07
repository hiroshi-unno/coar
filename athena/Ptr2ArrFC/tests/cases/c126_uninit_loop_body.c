/* p2a-expect: normal=1 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A variable of a loop's body starts uninitialised at every iteration:
   written at the first one only, it is read uninitialised at the second. */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int s = 0;
    for (int i = 0; i < 3; i++) {
        int t;
        __VERIFIER_nondet_int(); /* marks the position in the trace */
        if (i == 0) t = 1;
        s += t;
    }
    return s;
}
