/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* glibc's fpclassify macro, expanded as the preprocessed SV-COMP inputs
   hold it, selects by sizeof; the front end leaves the branch for the other
   sizes reading a temporary it no longer declares, and prints a
   prototype-less declaration of __builtin_isnan that clang refuses. The
   constant if becomes its live branch and the declaration is dropped. */
#include <stdio.h>
extern int __fpclassifyf(float);
extern int __fpclassify(double);
extern int __fpclassifyl(long double);
int main(void) {
  float f = 1.5f;
  double d = 0.0;
  int c = (sizeof (f) == sizeof (float) ? __fpclassifyf (f)
           : sizeof (f) == sizeof (double) ? __fpclassify (f) : __fpclassifyl (f));
  printf("%d %d\n", c == 4, __builtin_isnan(d) != 0);
  return 0;
}
