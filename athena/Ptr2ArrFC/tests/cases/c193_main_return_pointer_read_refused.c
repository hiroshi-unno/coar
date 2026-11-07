/* Expected: refused (exit status 2), kind int-pointer-cast. A pointer
   converted to an integer that main reads before returning it: the
   value is observed, so it is not made nondeterministic. */
static char buf[4];
int main(void) {
  int r = (int) (buf + 1);
  if (r == 0) return 1;
  return r;
}
