/* p2a-expect: normal=5 memory-safety=5 assume-safety=5 */
/* Casts between function pointer types: the value is kept, and a call at
   the function's own type after a round trip through another type is
   defined (C11 6.3.2.3p8). A truth test and a cast to _Bool of a function
   pointer. */
typedef void (*generic_t)(void);
static int five(int x) { return x + 4; }
int main(void) {
  generic_t g = (generic_t)five;
  int (*f)(int) = (int (*)(int))g;
  _Bool b = (_Bool)g;
  if (!g) return 1;
  return f(1) * b;
}
