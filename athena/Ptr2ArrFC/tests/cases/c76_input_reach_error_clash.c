/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 assume-safety=0 */
/* The program defines a reach_error that returns, calls it, and also has a
   function named like the one the reach-error markers rename it to; then it
   reads one cell past a block (valid-deref). With the reach-error markers
   its reach_error must get a name of its own, and only the violation may
   call reach_error(). */
#include <stdlib.h>
int calls;
void reach_error(void) { calls++; }
int __p2a_input_reach_error(int x) { return 2 * x; }
int main(void) {
    int *a = malloc(2 * sizeof(int));
    reach_error();
    a[0] = __p2a_input_reach_error(calls);
    a[1] = a[0];
    return a[calls + 1];
}
