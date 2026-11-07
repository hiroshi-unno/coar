/* p2a-expect: normal=0 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=0 */
/* The shape of sv-benchmarks' list-properties/simple-2.i: a list reachable
   only from a local of main when main returns. main's frame is gone after
   the return, so the list is not tracked (simple-2.i is
   false(valid-memtrack)). */
#include <stdlib.h>
struct node { struct node *next; int v; };
int main(void) {
    struct node *a = 0;
    int i;
    for (i = 0; i < 3; i++) {
        struct node *n = malloc(sizeof(struct node));
        n->v = i;
        n->next = a;
        a = n;
    }
    return 0;
}
