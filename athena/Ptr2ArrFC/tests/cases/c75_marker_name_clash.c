/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 assume-safety=0 */
/* The program has its own function named like a violation marker; the
   marker the output adds must take another name, and the program's function
   keep its meaning. The last read is one cell past the block: valid-deref. */
#include <stdlib.h>
int __p2a_violation_valid_deref(int x) { return x + 1; }
int main(void) {
    int *a = malloc(2 * sizeof(int));
    a[0] = __p2a_violation_valid_deref(0);
    a[1] = a[0];
    return a[__p2a_violation_valid_deref(1)];
}
