/* Terminates when a signed left shift that reaches the sign bit is undefined behaviour (the execution
   stops at it) and when it wraps (x << 1 is negative for x in [2^30, 2^31)); does not terminate when such
   a shift yields an arbitrary int, since a positive one enters a loop that never changes it. */
extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  if (x < 1073741824) return 0;
  int y = x << 1;
  while (y > 0) { }
  return 0;
}
