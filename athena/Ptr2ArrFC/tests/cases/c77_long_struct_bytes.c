/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 assume-safety=0 */
/* A structure holding a long and a pointer, on the heap and as a local
   whose address is taken, each also read byte by byte, so that both live in
   byte regions, whose layout is the translated one (a pointer becomes an
   int): the structure takes 16 bytes under LP64 and 12 under ILP32, and the
   field after the long moves from offset 8 to offset 4. */
#include <stdlib.h>
struct rec { long id; int *p; char tag; };
int main(void) {
    int x = 7;
    struct rec local;
    struct rec *h = malloc(sizeof(struct rec));
    unsigned char *hb = (unsigned char *)h;
    unsigned char *lb = (unsigned char *)&local;
    h->id = 258;
    h->p = &x;
    h->tag = 3;
    local = *h;
    int sum = hb[0] + hb[1] + lb[0] + *local.p + local.tag;
    free(h);
    return sum == 2 + 1 + 2 + 7 + 3 ? 0 : 1;
}
