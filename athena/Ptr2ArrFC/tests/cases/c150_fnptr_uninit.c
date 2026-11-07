/* p2a-expect: normal+uninit-nondet=0 */
/* Uninitialised function pointers: in a local, a structure field and an
   array element. With --uninit=nondet each starts at NULL, as a pointer
   does. */
struct ops { int (*op)(int); int k; };
static int id(int x) { return x; }
int main(void) {
  struct ops s;
  int (*p)(int);
  int (*t[2])(int);
  int r = 0;
  if (p == 0) r += 1;
  if (s.op == 0) r += 2;
  if (t[1] == 0) r += 4;
  p = id;
  return r == 7 ? p(0) : 1;
}
