extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
struct P { int x; int y; };
struct R { int a[5]; };
struct S { char c; int i; };
struct P swap(struct P p) { struct P r = { p.y, p.x }; return r; }
int third(struct R r) { return r.a[2]; }
int geti(struct S s) { return s.i + s.c; }
int main(void) {
  struct P p = { 1, 2 };
  struct P r = swap(p);
  struct R rr = { { 0, 0, 7, 0, 0 } };
  struct S s = { 1, 5 };
  __VERIFIER_assert(r.x == 2 && r.y == 1 && third(rr) == 7 && geti(s) == 6);
  return 0;
}
