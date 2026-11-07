#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main() {
  void *p = malloc(sizeof(int));
  if (__VERIFIER_nondet_int()) {
    p = 0;
  }
  return 0;
}
