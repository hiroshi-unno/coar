/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* GCC's unsigned overflow builtins store the wrapped result and return
   whether it overflowed; __builtin_object_size of an object it cannot size
   is (size_t)-1 for types 0 and 1 (the model always says so, which gcc also
   may); __VERIFIER_nondet_memory writes the bytes it is given. */
#include <stdio.h>
#include <limits.h>
#include <stddef.h>
extern void __VERIFIER_nondet_memory(void *p, size_t n);
int main(void) {
  unsigned int r;
  unsigned long rl;
  int o1 = __builtin_uadd_overflow(UINT_MAX, 2u, &r);
  printf("%d %u\n", o1, r);
  int o2 = __builtin_umull_overflow(1ul << 40, 1ul << 30, &rl);
  printf("%d %lu\n", o2, rl);
  int o3 = __builtin_usub_overflow(3u, 5u, &r);
  printf("%d %u\n", o3, r);
  int o4 = __builtin_umul_overflow(65536u, 65535u, &r);
  printf("%d %u\n", o4, r);
  char buf[4] = { 1, 2, 3, 4 };
  __VERIFIER_nondet_memory(buf, 2);
  printf("%d %d\n", buf[2], buf[3]);
  return 0;
}
