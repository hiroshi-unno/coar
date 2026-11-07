/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* memcpy, malloc and free called before the program declares them, as in
   CIL's output of the Linux drivers: GCC reads the calls with the
   builtins' types, and the declarations that follow agree with them. */
typedef __SIZE_TYPE__ size_t;
int copy3(char *d, char const *s) {
  void *r;
  r = memcpy((void *)d, (void const *)s, 3);
  return r == (void *)d;
}
char *dup3(char const *s) {
  char *p = (char *)malloc(3);
  if (p) copy3(p, s);
  return p;
}
extern void *memcpy(void *, void const *, size_t);
extern void *malloc(size_t);
extern void free(void *);
int main(void) {
  char a[3] = {'a', 'b', 'c'}, b[3];
  int ok = 0;
  ok = copy3(b, a);
  if (ok == 0) return 1;
  if (b[0] != 'a' || b[2] != 'c') return 2;
  char *p = dup3(a);
  if (p) {
    if (p[1] != 'b') return 3;
    free(p);
  }
  return 0;
}
