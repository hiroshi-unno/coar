/* p2a-expect: normal=1 memory-safety=1 assume-safety=1 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* An uninitialised pointer whose value is read (compared), never
   dereferenced: a violation of --uninit=check, not of the safety modes
   alone. With --uninit=nondet it starts NULL. */
int main(void) {
    int *p;
    if (p == 0) return 1;
    return 0;
}
