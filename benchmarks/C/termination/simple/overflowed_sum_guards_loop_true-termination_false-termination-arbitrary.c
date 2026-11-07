/* Terminates when an overflowing signed addition is undefined behaviour (the execution stops at it) and
   when it wraps (INT_MAX + 1 is INT_MIN, which skips the loop); does not terminate when the overflowing
   addition yields an arbitrary int, since a positive one enters a loop that never changes it. */
extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  int y = x + 1;
  if (x == 2147483647)
    while (y > 0) { }
  return 0;
}
