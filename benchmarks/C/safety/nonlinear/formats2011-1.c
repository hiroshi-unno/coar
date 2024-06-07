/* @name accelerate
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
  int vc = 0;
    /* the initial velocity */
  int fr = 1000;
    /* the initial force */
  int ac = 0.0005 * fr;
    /* the initial acceleration */
  while (1) {
    int fa = 0.5418 * vc * vc;
      /* the force control */
    fr = 1000 - fa;
    ac = 0.0005 * fr;
    vc = vc + ac;
    assert(vc < 49.61);
      /* the safety velocity */
  }
}
