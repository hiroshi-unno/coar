/* p2a-expect: normal=6 memory-safety=6 assume-safety=6 */
int twice(int x) { return 2 * x; }
int main(void) {
    int (*fp)(int) = twice;
    return fp(3);
}
