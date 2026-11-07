# 1 "c125_srcmap_lines.c"
/* The source map of the record on a preprocessed input: the positions are
   the physical lines and columns of this file, whatever the line markers
   say, so a statement under a marker naming another file (a header's
   function) keeps its position here, and one under a marker that moves the
   line number is not moved. */
# 1 "/usr/include/some_header.h" 1 3 4
static int clamp(int x) {
  while (x > 9) x = x - 3;
  return x;
}
# 7 "c125_srcmap_lines.c" 2
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
# 40 "c125_srcmap_lines.c"
int main(void) {
  int k = clamp(__VERIFIER_nondet_int());
  if (k == 4) reach_error();
  return 0;
}
