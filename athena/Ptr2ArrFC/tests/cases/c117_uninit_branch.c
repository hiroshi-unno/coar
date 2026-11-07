/* p2a-expect: normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A scalar written on one branch only: the read is uninitialised on the
   seeds that skip the write. */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int x;
    __VERIFIER_nondet_int(); /* the first draw of seeds 1-10 is even */
    if ((__VERIFIER_nondet_int() & 1)) x = 5;
    return x & 7;
}
