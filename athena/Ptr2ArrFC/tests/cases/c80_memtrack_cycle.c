/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* Two heap blocks that point to each other, and nothing else points to
   either: a cycle is not tracked by itself. */
#include <stdlib.h>
struct node { struct node *next; int v; };
struct node *g;
int main(void) {
    struct node *a = malloc(sizeof(struct node));
    struct node *b = malloc(sizeof(struct node));
    a->next = b;
    b->next = a;
    g = a;
    g = 0;
    a = 0;
    b = 0;
    return 0;
}
