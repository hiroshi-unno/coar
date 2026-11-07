/* p2a-expect: normal=0 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A scalar read before it is written: with --uninit=check the read reaches
   the marker; with --uninit=nondet it starts with a value of its type
   (zero when the output is run with the zero generators). */
int main(void) {
    int x;
    return x;
}
