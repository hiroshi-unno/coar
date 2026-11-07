/* The static object's cell is written after the marker, so it holds its
   value whatever the array held: the error is unreachable. */
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
int p2a_mem0[100];
void __p2a_arbitrary_p2a_mem0(void) { return; }
int main(void) {
  __p2a_arbitrary_p2a_mem0();
  p2a_mem0[1] = 7;
  if (p2a_mem0[1] != 7) reach_error();
  return 0;
}
