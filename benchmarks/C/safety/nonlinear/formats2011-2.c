/* @name cruise_control
   @require nonlinear invariants
   @from Craig Interpolation in the Presence of Non-linear Constraints
         Stefan Kupferschmid and Bernd Becker
         FORMATS 2011
   @used Generating Non-Linear Interpolants by Semidefinite Programming
         Liyun Dai, Bican Xia, and Naijun Zhan
         CAV 2013 */

extern error();

assert(int b) {
  if (!b) {
    error();
  }
}

main() {
  int vc = 10;
    /* the initial velocity */
  int fr = 1000;
    /* the initial force */
  int ac = 0.0005 * fr;
    /* the initial acceleration */
  while (1) {
    int fa = 0.5418 * vc * vc;
      /* the force control */
      /* @todo ask the authors how they implemented the controller */
    fr = 1000 - fa;
    ac = 0.0005 * fr;
    vc = vc + ac;
    assert(9.9 <= vc && vc <= 10.1);
      /* the safety velocity */
  }
}
