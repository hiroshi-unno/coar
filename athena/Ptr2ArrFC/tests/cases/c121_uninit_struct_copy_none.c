/* p2a-expect: normal=0 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A structure none of whose fields is written is copied whole: a
   violation at the copy. */
struct S { int a; int b; };
int main(void) {
    struct S s, t;
    t = s;
    return 0;
}
