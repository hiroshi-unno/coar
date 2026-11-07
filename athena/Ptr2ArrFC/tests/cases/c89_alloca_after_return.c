/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 memory-cleanup+reach-error=77 assume-safety=0 */
/* A block from alloca used after the function that allocated it returned:
   the block's lifetime ended with the function (valid-deref). Neither
   sanitizer reports it with its default settings, so the differential run
   reads the report as a false alarm; the expected status is the authority. */
#include <alloca.h>
int *make(void) {
    int *p = alloca(sizeof(int));
    *p = 3;
    return p;
}
int main(void) {
    int *q = make();
    return *q - 3;
}
