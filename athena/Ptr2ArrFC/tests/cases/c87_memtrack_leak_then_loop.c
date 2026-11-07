/* p2a-expect: normal=timeout memory-safety=timeout memory-safety+reach-error=timeout memory-cleanup=timeout memory-cleanup+reach-error=timeout assume-safety=timeout memory-safety+nonterminating=79 memory-cleanup+nonterminating=80 */
/* A block is lost, then the program runs for ever: the ends of the execution
   are never reached, so the check at the ends (MT1) does not see the leak. */
#include <stdlib.h>
int main(void) {
    int *p = malloc(sizeof(int));
    p = 0;
    for (;;) {
    }
    return 0;
}
