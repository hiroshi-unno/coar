#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
    struct node *h = malloc(sizeof(struct node));
    struct node **hp = &h;
    h->v = 1;
    int *q = malloc(4 * sizeof(int));
    int *r = &q[2];
    *r = 3;
    return (*hp)->v + q[2];
}
