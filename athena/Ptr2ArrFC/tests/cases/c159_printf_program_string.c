/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* printf printing strings the program holds, as Juliet's printLine does: each
   plain %s of such a pointer is printed by a function reading the characters
   one at a time, the rest by printf with its own arguments; the output is the
   same characters (the differential run compares it). A string literal under
   %s stays with printf. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static void printLine(const char *line) { printf("%s\n", line); }
int main(void) {
  char *name = malloc(8);
  strcpy(name, "abc");
  char local[4] = "xy";
  printf("id=%d name=%s tag=%s %s %%!\n", 7, name, local, "lit");
  printLine(name);
  free(name);
  return 0;
}
