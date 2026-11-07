/* p2a-expect: normal=0 normal+uninit-check=0 memory-safety+uninit-check=0 assume-safety+uninit-check=0 */
/* A variable whose address is taken, read through the pointer before it is
   written: not a violation of --uninit=check (C11 makes it unspecified,
   not undefined). */
int main(void) {
    int x;
    int *p = &x;
    return *p;
}
