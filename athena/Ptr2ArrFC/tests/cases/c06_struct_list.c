#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
    struct node *h = (struct node *)malloc(sizeof(struct node));
    h->v = 1;
    h->next = 0;
    struct node *n = malloc(sizeof(struct node));
    n->v = 2;
    n->next = h;
    int s = 0;
    struct node *c = n;
    while (c != 0) { s += c->v; c = c->next; }
    return s;
}
