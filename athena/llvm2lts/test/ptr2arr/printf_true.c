/* printf, puts and putchar change no variable; a used result is arbitrary. */
extern int printf(const char *, ...);
extern int puts(const char *);
extern int putchar(int);
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
int main(void) {
  int x = __VERIFIER_nondet_int();
  if (x < 0 || x > 10) return 0;
  printf("x=%d\n", x);
  puts("hello");
  int r = putchar('a');
  if (x > 10) reach_error();
  return r - r;
}
