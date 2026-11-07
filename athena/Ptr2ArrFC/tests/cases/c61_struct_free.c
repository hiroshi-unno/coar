#include <stdlib.h>
struct node { int v; struct node *next; };
int main(void) {
    struct node *h = malloc(sizeof(struct node));
    h->v = 1;
    free(h);
    return 0;
}
