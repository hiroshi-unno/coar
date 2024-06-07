/* @name LCM-GCD Algorithm
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
  int x1, x2, y1, y2, y3, y4;
  assume(y1 == x1 && y2 == y3 && y3 == x2 && y4 == 0);
  while (y1 != y2) {
    while (y1 > y2) {
      y1 = y1 - y2;
      y4 = y4 + y3;
    }
    while (y2 > y1) {
      y2 = y2 - y1;
      y3 = y3 + y4;
    }
  }
  assert(y1 == gcd(x1, x2) && y3 + y4 == lcm(x1, x2));
}
