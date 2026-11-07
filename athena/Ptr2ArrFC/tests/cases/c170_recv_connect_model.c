/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* recv returns some r in -1..len and writes r bytes; connect and bind
   return 0 or -1 (the input program's calls fail on a bad descriptor). */
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
int main(void) {
  char buf[10];
  struct sockaddr_in a;
  memset(&a, 0, sizeof(a));
  int c = connect(-1, (struct sockaddr *)&a, sizeof(a));
  if (c != 0 && c != -1) return 3;
  int b = bind(-1, (struct sockaddr *)&a, sizeof(a));
  if (b != 0 && b != -1) return 4;
  long r = recv(-1, buf, sizeof(buf) - 1, 0);
  if (r < -1 || r > 9) return 5;
  if (r >= 0) buf[r] = 0;
  return 0;
}
