/* p2a-expect: normal=0 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A structure none of whose fields is written is passed by value: a
   violation at the call, though the callee reads nothing. */
struct S { int a; int b; };
int f(struct S v) { return 0; }
int main(void) {
    struct S s;
    return f(s);
}
