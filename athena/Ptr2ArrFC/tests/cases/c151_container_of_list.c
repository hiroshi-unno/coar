/* p2a-expect: normal=6 memory-safety=6 memory-safety+reach-error=6 memory-cleanup=6 memory-cleanup+reach-error=6 assume-safety=6 */
/* An intrusive list as the Linux kernel writes it: each element embeds a
   list_head, here inside a nested member after a pointer member, and
   container_of steps back from the list_head to the element with offsetof
   written as the address of a member of a null pointer. The pointer member
   makes the input's offset (16 under LP64) differ from the translated one
   (8). Every block is freed. */
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
