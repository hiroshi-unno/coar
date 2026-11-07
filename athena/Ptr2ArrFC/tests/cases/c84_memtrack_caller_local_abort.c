/* p2a-expect: normal=abort memory-safety=abort memory-safety+reach-error=abort memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=abort */
/* A block reachable only from a local of main when a function main calls
   aborts: main's frame is still on the call stack, so the block is tracked
   at the abort (the local is made an object so that the check, in the
   callee, sees it); it is left allocated, which valid-memcleanup reports. */
#include <stdlib.h>
struct node { struct node *next; int v; };
void fail(int v) {
    if (v == 7) abort();
}
int main(void) {
    struct node *a = malloc(sizeof(struct node));
    a->v = 7;
    a->next = malloc(sizeof(struct node));
    fail(a->v);
    free(a->next);
    free(a);
    return 0;
}
