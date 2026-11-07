#include <stdlib.h>
struct node { int v; struct node *next; };
int length(struct node *l) {
    int n = 0;
    while (l != NULL) { n++; l = l->next; }
    return n;
}
int main(void) {
    struct node *l = NULL;
    int i;
    for (i = 0; i < 3; i++) {
        struct node *m = malloc(sizeof(struct node));
        m->v = i;
        m->next = l;
        l = m;
    }
    return length(l);
}
