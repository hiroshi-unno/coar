/* p2a-expect: memory-safety=77 memory-safety+reach-error=77 memory-cleanup=77 assume-safety=0 */
/* printf("%s") of characters with no 0 inside their block reads past its
   end: valid-deref, as strlen would be. */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  char *s = malloc(4);
  s[0] = 'a'; s[1] = 'b'; s[2] = 'c'; s[3] = 'd';
  printf("%s\n", s);
  free(s);
  return 0;
}
