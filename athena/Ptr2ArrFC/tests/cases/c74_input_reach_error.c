/* p2a-expect: normal=134 memory-safety=134 memory-safety+reach-error=134 memory-cleanup=80 memory-cleanup+reach-error=77 assume-safety=134 */
/* The shape of sv-benchmarks' list-ext.i: the program defines its own
   reach_error, which fails an assertion (__assert_fail aborts), and reaches it
   without violating memory safety. It is not a memory-safety violation: the
   output must abort as the input does, never stop at a violation marker. */
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "c74_input_reach_error.c", 3, "reach_error"); }
#include <stdlib.h>
struct node { int h; struct node *n; };
int main(void) {
    struct node *a = malloc(sizeof(struct node));
    struct node *b = malloc(sizeof(struct node));
    a->h = 1; a->n = b;
    b->h = 2; b->n = 0;
    struct node *p = a;
    int sum = 0;
    while (p) { sum += p->h; p = p->n; }
    if (sum == 3) { ERROR: {reach_error(); abort();} }
    return 0;
}
