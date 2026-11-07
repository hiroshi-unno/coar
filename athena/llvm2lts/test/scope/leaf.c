/* glibc's declarations as a preprocessed task carries them: __leaf__, which
   clang 19 reads as nocallback, on __assert_fail and abort. */
extern void __assert_fail(const char *, const char *, unsigned int, const char *)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
extern void abort(void) __attribute__((__nothrow__, __leaf__)) __attribute__((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void reach_error() { __assert_fail("0", "leaf.c", 3, "reach_error"); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x < 0) abort();
  if (x == 5) reach_error();
  return 0;
}
