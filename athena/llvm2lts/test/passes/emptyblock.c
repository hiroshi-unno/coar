extern int __VERIFIER_nondet_int(void);
void rec(int x, int y)
{
  if (x <= 23)
    if (x >= -42) {
      rec(2 * y - 2, x + 1);
    }
  return;
}
int main(void)
{
  int n = __VERIFIER_nondet_int();
  rec(n, n + 1);
  return 0;
}
