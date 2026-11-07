/* p2a-expect: normal=1 memory-safety=1 normal+uninit-check=77 memory-safety+uninit-check=82 memory-safety+uninit-check+reach-error=77 assume-safety+uninit-check=0 */
/* A pointer variable of main whose address is never taken, made an object
   under --memory-safety so that the end check below sees it as a root:
   still checked by --uninit=check (it is read before it is written). */
#include <stdlib.h>
void g(int *q) {
    free(q);
    exit(1);
}
int main(void) {
    int *p;
    int *q = malloc(sizeof(int));
    if (p != 0) *q = 1;
    g(q);
    return 0;
}
