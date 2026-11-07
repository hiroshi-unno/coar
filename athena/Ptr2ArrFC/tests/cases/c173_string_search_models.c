/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* memcmp, strncmp, strchr, strrchr and memchr modelled as functions added to
   the program: on literal and stack data they give what the C library gives
   (the signs of the comparisons, the positions found). */
#include <stdio.h>
#include <string.h>
static int sign(int v) { return v < 0 ? -1 : v > 0; }
int main(void) {
  char a[6] = "abcde", b[6] = "abxde";
  const char *s = "path/to/file";
  printf("%d %d %d\n", sign(memcmp(a, b, 5)), sign(memcmp(a, b, 2)), sign(memcmp(b, a, 3)));
  printf("%d %d %d\n", sign(strncmp(a, b, 2)), sign(strncmp(a, b, 5)), sign(strncmp("ab", "abc", 5)));
  printf("%d %d %d\n", (int)(strchr(s, '/') - s), (int)(strrchr(s, '/') - s), strchr(s, 'z') == NULL);
  printf("%d %d\n", (int)(strchr(s, 0) - s), (int)((char *)memchr(a, 'd', 5) - a));
  printf("%d\n", memchr(a, 'q', 5) == NULL);
  return 0;
}
