#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main() {
  int *a = malloc(4 * sizeof(int));
  int k = __VERIFIER_nondet_int();
  if (a != 0 && k >= 0 && k <= 4) {
    a[k] = 1;
  }
  free(a);
  if (k == 2) {
    free(a);
  }
  return 0;
}
