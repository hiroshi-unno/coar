/* The source map of the record with --check-overflow: the call of each
   check is a no-overflow target, placed at the statement or full expression
   that holds the operation: an expression statement, a condition, a for
   clause, a returned value, an initialiser, and a macro's expansion. The
   input's reach_error is no target here (it is renamed). */
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
#define TWICE(x) ((x) + (x))
int main(void) {
  int n = __VERIFIER_nondet_int();
  int k = n * 3;
  int i;
  for (i = 0; i < 10; i = i + 1) n = n - 1;
  if (n + 1 > 5) k = 0;
  if (k == 99) reach_error();
  k = TWICE(n);
  return k - 2;
}
