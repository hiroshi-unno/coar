/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* A list reachable from a global when main returns: tracked (no
   valid-memtrack violation), but left allocated (valid-memcleanup). */
#include <stdlib.h>
struct node { struct node *next; int v; };
struct node *head;
int main(void) {
    int i;
    for (i = 0; i < 3; i++) {
        struct node *n = malloc(sizeof(struct node));
        n->v = i;
        n->next = head;
        head = n;
    }
    return 0;
}
