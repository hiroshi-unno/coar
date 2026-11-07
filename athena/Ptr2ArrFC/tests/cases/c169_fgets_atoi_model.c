/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* fgets writes at most n-1 characters and a 0 when it returns its buffer;
   atoi reads what C says it reads (the literals give the same values as
   the C library). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(void) {
  char buf[8];
  buf[7] = 'x';
  if (fgets(buf, 8, stdin) != NULL) {
    if (strlen(buf) > 7) return 3;
    (void)atoi(buf);
  }
  if (atoi(" \t-42xyz") != -42) return 4;
  if (atoi("+17") != 17) return 5;
  if (atoi("2147483647") != 2147483647) return 6;
  if (atoi("-2147483648") != -2147483647 - 1) return 7;
  if (atoi("abc") != 0) return 8;
  return 0;
}
