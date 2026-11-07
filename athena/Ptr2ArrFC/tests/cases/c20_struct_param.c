#include <stdlib.h>
struct node { int v; struct node *next; };
int sum(struct node *l) { int s = 0; while (l) { s += l->v; l = l->next; } return s; }
int main(void) {
    struct node *h = malloc(sizeof(struct node));
    h->v = 3; h->next = NULL;
    return sum(h);
}
