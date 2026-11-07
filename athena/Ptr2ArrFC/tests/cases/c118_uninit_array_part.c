/* p2a-expect: normal+uninit-check=3 memory-safety+uninit-check=3 assume-safety+uninit-check=3 */
/* An array (never used as a pointer) with some elements written: a read of
   a written element is not a violation, of the others it is. */
extern int __VERIFIER_nondet_int(void);
int main(void) {
    int a[4];
    a[0] = 1;
    a[2] = 3;
    __VERIFIER_nondet_int(); /* the first draw of seeds 1-10 is even */
    int i = __VERIFIER_nondet_int() & 3;
    return a[i];
}
