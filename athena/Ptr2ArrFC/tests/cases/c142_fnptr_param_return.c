/* p2a-expect: normal=0 memory-safety=0 assume-safety=0 */
/* Function pointers as parameters and results, a function returning one,
   and an address-taken function pointer variable read through a pointer
   to it (so the number lives in a region cell). */
typedef void (*step_t)(int *);
static void up(int *x) { *x += 3; }
static void down(int *x) { *x -= 1; }
static step_t choose(int c) { return c ? up : down; }
static void apply_n(step_t f, int n, int *x) { for (int i = 0; i < n; i++) f(x); }
int main(void) {
  int x = 0;
  apply_n(choose(1), 3, &x);   /* 9 */
  step_t s = choose(0);
  step_t *ps = &s;
  apply_n(*ps, 2, &x);         /* 7 */
  *ps = up;
  (*ps)(&x);                   /* 10 */
  return x == 10 ? 0 : 1;
}
