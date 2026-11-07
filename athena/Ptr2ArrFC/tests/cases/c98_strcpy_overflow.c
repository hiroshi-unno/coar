/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 assume-safety=0 */
/* strcpy past the end of its destination: valid-deref. */
#include <stdlib.h>
#include <string.h>
int main(void) {
    char *d = malloc(4);
    strcpy(d, "abcdef");
    free(d);
    return 0;
}
