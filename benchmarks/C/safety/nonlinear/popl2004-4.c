/* @name Hardware Style Division Algorithm
   @require nonlinear invariants
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
  double y1, y2, y3, y4, x1, x2, q, r;
  assume(y1 == x1 && y2 == x2 && y3 == 1 && y4 == 0);
  while (y1 >= y2) {
    y2 = 2 * y2;
    y3 = 2 * y3;
  }
  while (1) {
    if (y1 >= y2) {
      y1 = y1 - y2;
      y4 = y4 + y3;
    }
    if (y3 == 1) {
      q = y4;
      r = y1;
      break;
    }
    y2 = y2 / 2;
    y3 = y3 / 2;
  }
  assert(x1 == r + x2 * q);
}
