/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 assume-safety=0 */
/* A field read after its block is released: valid-deref. */
#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
    struct node *n = malloc(sizeof(struct node));
    n->v = 3;
    n->next = 0;
    free(n);
    return n->v;
}
