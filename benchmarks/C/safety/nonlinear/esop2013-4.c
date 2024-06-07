/* @from A Data Driven Approach for Algebraic Loop Invariants
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
  int n;
  int i = 0;
  int a[n];
  a[0] = 0;
  assume(n > 0);
  while (i != n) {
    i = i + 1;
    a[i] = a[i - 1] + 1;
  }
  assert(a[n] == n);
}
