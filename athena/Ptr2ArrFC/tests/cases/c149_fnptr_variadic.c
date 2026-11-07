/* Forms that stay refused: a pointer to a variadic function. */
#include <stdio.h>
int main(void) {
  int (*pf)(const char *, ...) = printf;
  return pf("") ;
}
