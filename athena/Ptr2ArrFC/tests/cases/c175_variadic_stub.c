/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* A variadic function whose body never reads its variable arguments, as the
   driver tasks' printk and dev_err stubs: its "..." and the extra arguments
   of its calls are dropped, pointers among them included. */
#include <stdlib.h>
int printk(const char *fmt, ...) { return 0; }
int dev_err(void *dev, const char *fmt, ...) { (void)dev; return 1; }
int main(void) {
  int *p = malloc(sizeof(int));
  *p = 3;
  int r = printk("value %d at %p\n", *p, p);
  r += dev_err(p, "error %s\n", "x");
  free(p);
  return r == 1 ? 0 : 1;
}
