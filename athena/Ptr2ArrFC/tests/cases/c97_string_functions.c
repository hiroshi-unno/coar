/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 memory-cleanup+reach-error=0 assume-safety=0 */
/* strlen, strcmp, strcpy, strncpy and strcat over character arrays, a
   string literal among the arguments. */
#include <string.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
    char a[16];
    char b[16];
    int n = __VERIFIER_nondet_int();
    strcpy(a, "abc");
    strncpy(b, a, 8);
    if (n > 3) b[1] = 'x';
    strcat(a, "de");
    if (strlen(a) != 5) return 1;
    if (strcmp(a, "abcde") != 0) return 2;
    if (n > 3) {
        if (strcmp(a, b) >= 0) return 3;
    } else {
        if (strcmp(a, b) <= 0) return 4;
    }
    return 0;
}
