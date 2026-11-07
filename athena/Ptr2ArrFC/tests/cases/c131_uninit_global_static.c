/* p2a-expect: normal=0 normal+uninit-check=0 memory-safety+uninit-check=0 assume-safety+uninit-check=0 */
/* Globals and static locals start at zero in C: no mode reports or changes
   them. */
int g;
int arr[3];
int f(void) {
    static int c;
    return c++;
}
int main(void) {
    f();
    return g + arr[2] + f() - 1;
}
