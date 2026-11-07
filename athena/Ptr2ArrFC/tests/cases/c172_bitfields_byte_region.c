/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* Bit-fields of a structure in a byte region (memcpy between structures of
   different types makes the region one of bytes): a field over two bytes,
   a signed field read negative, an unnamed padding field, a whole-structure
   copy; the values printed are the input's. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct A { unsigned char a; unsigned char b; unsigned short c; unsigned int d; };
struct B {
  unsigned char a;
  unsigned char b : 2;
  unsigned char c : 2;
  unsigned char d : 4;
  unsigned short e : 11;
  signed short f : 5;
  int : 3;
  unsigned int g : 7;
};
int main(void) {
  struct A x = { 1, 0xB7, 0x1234, 0x89ABCDEF };
  struct B *p = malloc(sizeof(struct B));
  memcpy(p, &x, sizeof(struct B) < sizeof(x) ? sizeof(struct B) : sizeof(x));
  printf("%u %u %u %u %u %d %u\n", p->a, p->b, p->c, p->d, p->e, p->f, p->g);
  p->c = 1;
  p->f = -3;
  p->e = 2047;
  p->g = 200;
  struct B q = *p;
  q.d = 9;
  *p = q;
  printf("%u %u %u %u %u %d %u\n", p->a, p->b, p->c, p->d, p->e, p->f, p->g);
  free(p);
  return 0;
}
