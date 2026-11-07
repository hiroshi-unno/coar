/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* fscanf and scanf with integer conversions return some m in -1..k and
   store through the first m pointers only; whatever the input (stdin is
   empty for the input program, the model draws the values), these hold. */
#include <stdio.h>
int main(void) {
  int a = 5;
  long b = 6;
  size_t c = 7;
  int m = fscanf(stdin, "%d %ld", &a, &b);
  if (m < -1 || m > 2) return 3;
  if (m < 1 && a != 5) return 4;
  if (m < 2 && b != 6) return 5;
  int n = scanf("%*d %zu", &c);
  if (n < -1 || n > 1) return 6;
  if (n < 1 && c != 7) return 7;
  return 0;
}
