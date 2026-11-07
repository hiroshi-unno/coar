/* p2a-expect: normal=7 memory-safety=7 assume-safety=7 */
/* A call through a function pointer whose candidate is a static function
   defined after the call and declared nowhere before it: the program only
   takes its address later, which needs no declaration. The direct call that
   replaces the call through the pointer needs one. */
static int apply(int (*f)(int), int x) { return f(x); }
static int inc(int x) { return x + 1; }
int main(void) { return apply(inc, 6); }
