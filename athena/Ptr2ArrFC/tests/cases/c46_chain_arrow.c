#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
    struct node *a = malloc(sizeof(struct node));
    struct node *b = malloc(sizeof(struct node));
    a->next = b;
    b->v = 4;
    return a->next->v;
}
