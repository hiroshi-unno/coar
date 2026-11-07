/* Terminates when INT_MIN / -1 is undefined behaviour (the execution stops at it; x86 traps there even
   under -fwrapv); does not terminate when it yields an arbitrary int, since a positive quotient enters a
   loop that never changes it. */
extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (y != -1) return 0;
  int q = x / y;
  if (x == -2147483647 - 1)
    while (q > 0) { }
  return 0;
}
