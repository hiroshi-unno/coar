/* p2a-expect: normal=1 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=1 */
/* The shape of sv-benchmarks' memsafety/global-atexit-2.i, with the exit
   taken: exit runs the functions atexit registered, the latest first;
   free_g1 releases the block g points to and clears g, so the block *g
   pointed to is no longer tracked when the check runs after them
   (global-atexit-2.i is false(valid-memtrack)). */
#include <stdlib.h>
int **g = 0;
void free_g1(void) {
    free(g);
    g = 0;
}
void free_g2(void) {
    if (g != 0) free(*g);
}
void h(void) {
    exit(1);
}
void f(void) {
    *g = (int *)malloc(sizeof(int));
    atexit(free_g1);
    h();
}
int main(void) {
    g = (int **)malloc(sizeof(int *));
    atexit(free_g2);
    f();
    free(*g);
    free(g);
    g = 0;
    return 0;
}
