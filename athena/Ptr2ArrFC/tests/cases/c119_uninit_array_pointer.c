/* p2a-expect: normal=1 normal+uninit-check=1 memory-safety+uninit-check=1 assume-safety+uninit-check=1 */
/* An array used as a pointer (passed to a function) is an object, outside
   --uninit=check: reading its unwritten element through the pointer is not
   reported. With --uninit=nondet its elements start nondeterministic. */
int sum(int *p, int n) {
    int s = 0;
    for (int k = 0; k < n; k++) s += p[k];
    return s;
}
int main(void) {
    int a[3];
    a[0] = 1;
    return sum(a, 2);
}
