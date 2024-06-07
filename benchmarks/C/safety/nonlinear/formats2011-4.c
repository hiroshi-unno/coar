/* @name henon
   @require nonlinear invariants
   @from Craig Interpolation in the Presence of Non-linear Constraints
         Stefan Kupferschmid and Bernd Becker
         FORMATS 2011 */

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

int safe(double x, double y) {
  return 0/* ToDo: ask the authors which intervals they used */;
}

main() {
  double x, y;
  double a = 1.25;
  double b = 0.3;
  assume(safe(x, y));
  while(1) {
    double tmp = y + 1 - a * x * x;
    y = b * x;
    x = tmp;
    assert(safe(x, y));
  }
}
