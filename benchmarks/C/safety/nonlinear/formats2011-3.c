/* @name logistic
   @require nonlinear invariants
   @from Craig Interpolation in the Presence of Non-linear Constraints
         Stefan Kupferschmid and Bernd Becker
         FORMATS 2011
   @used Generating Non-Linear Interpolants by Semidefinite Programming
         Liyun Dai, Bican Xia, and Naijun Zhan
         CAV 2013 */

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

int safe(double x) {
  return 0.78 <= x && x <= 0.82 || 0.48 <= x && x <= 0.52;
}

main() {
  double x;
  double r = 3.2;
  assume(safe(x));
  while(1) {
    x = r * x * (1 - x);
    assert(safe(x));
  }
}
