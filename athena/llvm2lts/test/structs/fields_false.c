extern int __VERIFIER_nondet_int(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!cond) { reach_error(); abort(); } }
struct inner { int v[3]; char tag; };
struct outer { long id; struct inner in; };
struct outer g;
struct node { int val; int next; } nodes[4];
int main(void) {
  struct outer o = { 0 };
  struct outer o2;
  int k = __VERIFIER_nondet_int();
  if (k < 0 || k >= 3) return 0;
  o.in.v[k] = 9;
  o2 = o;
  g = o2;
  nodes[k].val = 4;
  nodes[k].next = k + 1;
  __VERIFIER_assert(g.in.v[k] == 9 && o2.id == 1 && nodes[k].val + nodes[k].next == k + 5);
  return 0;
}
