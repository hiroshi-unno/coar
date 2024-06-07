/* @name Leaking gas burner
   @from The Algorithmic Analysis of Hybrid Systems
         R. Alur, C. Courcoubetis, N. Halbwachs, T. A. Henzinger, P.-H. Ho, X. Nicollin, A. Olivero, J. Sifakis, and S. Yovine
         TCS 1995
   @used Craig Interpolation in the Presence of Non-linear Constraints
         Stefan Kupferschmid and Bernd Becker
         FORMATS 2011 */

extern int dt();
extern error();
extern int nondet_bool();

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
  int x = 0;
  int y = 0;
  int z = 0;
  int state = 0;
  while(1) {
    int dx, dy, dz;
    if (state == 0) {
      dx = dt();
      dy = dt();
      dz = dt();
      assume(x <= 1);
      if (nondet_bool()) {
        x = 0;
        state = 1;
      }
    } else if (state == 1) {
      dx = dt();
      dy = dt();
      dz = 0;
      if (x >= 30) {
        x = 0;
        state = 0;
      }
    }
    assert(!(y >= 60) || 20 * z <= y);
    x += dx;
    y += dy;
    z += dz;
  }
}
