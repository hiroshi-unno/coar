/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 memory-cleanup+reach-error=0 assume-safety=0 */
/* A pointer field written through a pointer to the field and read as the
   field: the structure is in a byte region (a pointer addresses a field of
   a cell), where both paths must see one shadow. */
#include <stdlib.h>
struct box { long id; int *p; };
static void fill(int **pp) {
    *pp = malloc(sizeof(int));
}
int main(void) {
    struct box *b = malloc(sizeof(struct box));
    b->id = 1;
    fill(&b->p);
    *b->p = 3;
    struct box copy = *b;
    int v = *copy.p;
    free(b->p);
    free(b);
    return v - 3;
}
