/* p2a-expect: normal=134 normal+uninit-check=134 memory-safety+uninit-check=134 assume-safety+uninit-check=134 */
/* The input's own reach_error is an ordinary function under
   --uninit=check: it is renamed, and only an uninitialised read calls the
   marker. Here the input reaches its own reach_error first. */
#include <stdlib.h>
void reach_error(void) { abort(); }
int main(void) {
    int x;
    reach_error();
    return x;
}
