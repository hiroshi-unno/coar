/* Input of tests/overflow_conds.sh: every operation ptr2arr --check-overflow
   checks, at int and long long, so that the output holds each check
   function. */
extern int __VERIFIER_nondet_int(void);
extern long long __VERIFIER_nondet_longlong(void);
int main(void) {
  int a = __VERIFIER_nondet_int(), b = __VERIFIER_nondet_int();
  long long x = __VERIFIER_nondet_longlong(), y = __VERIFIER_nondet_longlong();
  int r = a + b; r = a - b; r = a * b; r = -a; r = a / b; r = a << b;
  long long s = x + y; s = x - y; s = x * y; s = -x; s = x / y; s = x << b;
  return r + (int)s;
}
