/* @require nonlinear invariants
   @from Non-linear loop invariant generation using Gr\"{o}bner bases
         Sriram Sankaranarayanan, Henny B. Sipma, and Zohar Manna
         POPL 2004
   @used A Data Driven Approach for Algebraic Loop Invariants
         Rahul Sharma, Saurabh Gupta, Bharath Hariharan, Alex Aiken, Percy Liang, and Aditya V. Nori
         ESOP 2013 */

extern error();

assume(int b) {
  if (!b) {
    assume(b);
  }
}

assert(int b) {
  if (!b) {
    error();
  }
}

main() {
  int i, j, s, j0;
  assume(s == 0 && j == j0);
  while (j != 0) {
    s = s + i;
    j = j - 1;
  }
  assert(s == i * j0);
}
