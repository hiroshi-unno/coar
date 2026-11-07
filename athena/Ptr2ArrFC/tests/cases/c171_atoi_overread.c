/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 assume-safety=0 */
/* atoi of digits with no non-digit inside their block reads past its end:
   valid-deref, as in the input. */
#include <stdlib.h>
int main(void) {
  char *s = malloc(3);
  s[0] = '1'; s[1] = '2'; s[2] = '3';
  int v = atoi(s);
  free(s);
  return v == 123 ? 0 : 1;
}
