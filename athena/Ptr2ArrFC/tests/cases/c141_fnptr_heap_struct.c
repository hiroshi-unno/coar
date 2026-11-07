/* p2a-expect: normal=0 memory-safety=0 assume-safety=0 */
/* Function pointers in structure fields, in heap blocks reached through a
   linked list; the callbacks take and return data pointers, so the calls
   through them pass region indices. */
#include <stdlib.h>
struct node {
  int val;
  int *(*pick)(struct node *);
  struct node *next;
};
static int *self_val(struct node *n) { return &n->val; }
static int *next_val(struct node *n) { return n->next ? &n->next->val : &n->val; }
int main(void) {
  struct node *head = 0;
  for (int i = 0; i < 4; i++) {
    struct node *n = malloc(sizeof *n);
    n->val = i;
    n->pick = (i % 2) ? next_val : self_val;
    n->next = head;
    head = n;
  }
  int sum = 0;
  for (struct node *n = head; n; n = n->next) {
    int *q = n->pick(n);
    *q += 1;
    sum += *q;
  }
  while (head) { struct node *n = head->next; free(head); head = n; }
  return sum == 10 ? 0 : 1;
}
