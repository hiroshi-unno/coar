/* The shape the new Ptr2Arr writes: a region array, its marker called at the
   head of main before the static object (cell 1) is written, and a cell past
   the static objects read before any write.  The cell is arbitrary, so the
   error is reachable. */
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__((__noreturn__));
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }
int p2a_mem0[100];
int p2a_mem0_free = 2;
void __p2a_arbitrary_p2a_mem0(void) { return; }
int main(void) {
  __p2a_arbitrary_p2a_mem0();
  p2a_mem0[1] = 7;
  int p = p2a_mem0_free;
  p2a_mem0_free += 1;
  if (p2a_mem0[1] != 7) reach_error();
  if (p2a_mem0[p] != 0) reach_error();
  return 0;
}
