/* The source map of the record on loops: the head of a for and a while loop
   is a loop-head at the keyword, its condition a branch there; a do loop's
   head is not before its condition, so it is "other" and only its condition
   is a branch; a condition with && is several conditionals, none a branch;
   continue, nested loops, several statements on one line, a tab and a
   multibyte character before a statement (columns are bytes), and two
   calls of reach_error, each an unreach-call target. */
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);
int main(void) {
  int i, j, s = 0, n = __VERIFIER_nondet_int();
  for (i = 0; i < n; i++) {
    if (i == 3) continue;
    for (j = 0; j < i; j = j + 1) s += j;
  }
  while (s > 100) s = s - 7;
  do { s++; } while (s < 5);
  while (n > 0 && s > 0) { n--; s--; }
  for (;;) { if (n++ > 3) break; }
  int a = 1; int b = 2; a = a + b; if (a) b = 0; else b = 1;
	if (b == 9) a = 2;
  /* é */ if (a == 7) reach_error();
  if (s == 8) { reach_error(); }
  return 0;
}
