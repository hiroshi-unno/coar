/* p2a-expect: normal=3 memory-safety=79 memory-safety+reach-error=77 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=3 */
/* The list of c151, with the first element unlinked and its last pointer
   dropped without a free: a block is lost (valid-memtrack), then the others
   are freed through container_of. */
#include <stddef.h>
#include <stdlib.h>
struct list_head { struct list_head *next, *prev; };
struct item { int *tag; struct { int pad; struct list_head list; } in; int v; };
#define my_offsetof(T, m) ((size_t) &((T *)0)->m)
#define container_of(p, T, m) ((T *)((char *)(p) - my_offsetof(T, m)))
static struct list_head head = { &head, &head };
static void add(struct list_head *n) {
  n->next = head.next;
  n->prev = &head;
  head.next->prev = n;
  head.next = n;
}
int main(void) {
  for (int i = 1; i <= 3; i++) {
    struct item *it = malloc(sizeof *it);
    it->tag = 0;
    it->v = i;
    add(&it->in.list);
  }
  struct list_head *first = head.next;
  head.next = first->next;
  first->next->prev = &head;
  first = 0;
  int s = 0;
  struct list_head *p = head.next;
  while (p != &head) {
    struct list_head *nx = p->next;
    struct item *it = container_of(p, struct item, in.list);
    s += it->v;
    free(it);
    p = nx;
  }
  head.next = head.prev = &head;
  return s;
}
