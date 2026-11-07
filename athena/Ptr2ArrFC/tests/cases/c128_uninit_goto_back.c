/* p2a-expect: normal=3 */
/* A goto jumps back over the declaration of x, which C makes indeterminate
   again: refused by --uninit=check and --uninit=nondet (status 2). */
int main(void) {
    int n = 0;
L:
    n++;
    int x;
    if (n < 3) {
        x = n;
        goto L;
    }
    x = n;
    return x;
}
