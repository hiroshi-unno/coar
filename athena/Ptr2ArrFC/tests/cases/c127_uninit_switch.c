/* p2a-expect: normal+uninit-nondet=10 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A variable declared in a switch's body, entered by a case label at each
   iteration: written on the first entry, it is read uninitialised on the
   second (C makes it indeterminate at each entry into the block). */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int s = 0;
    for (int k = 0; k < 2; k++) {
        __VERIFIER_nondet_int(); /* marks the position in the trace */
        switch (k) {
        case 0:
            s++;
            int w;
            w = 5;
            s += w;
            break;
        case 1:
            s += w + 4;
            break;
        }
    }
    return s;
}
