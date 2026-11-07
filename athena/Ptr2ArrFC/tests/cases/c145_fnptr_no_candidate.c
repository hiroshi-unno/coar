/* p2a-expect: normal=3 memory-safety=3 assume-safety=3 */
/* A call through a function pointer type no address-taken function has: the
   call has no candidate, and is reached only on NULL (here: never). */
static int f(int x) { return x; }
int main(void) {
  int (*p)(int) = f;
  long (*q)(long, long) = 0;
  int r = p(3);
  if (q) r = (int)q(1, 2);
  return r;
}
