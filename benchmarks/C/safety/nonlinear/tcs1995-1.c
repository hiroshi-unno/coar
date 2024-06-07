/* @name Thermostat
   @from The Algorithmic Analysis of Hybrid Systems
         R. Alur, C. Courcoubetis, N. Halbwachs, T. A. Henzinger, P.-H. Ho, X. Nicollin, A. Olivero, J. Sifakis, and S. Yovine
         TCS 1995
   @used Craig Interpolation in the Presence of Non-linear Constraints
         Stefan Kupferschmid and Bernd Becker
         FORMATS 2011 */

extern int dt();
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
  int min;
  int max;
  int k;
  int h;
  int x = max;
  int state = 0;
  while(1) {
    int dx;
    if (state == 0) {
      dx = -k * x * dt();
      assume(x >= min);
      if (x == min) state = 1;
    } else if (state == 1) {
      dx = k * (h - x) * dt();
      assume(x <= max);
      if (x == max) state = 0;
    }
    assert(min <= x && x <= max); /* ToDo: need some assumption on min, max, k, h? */
    x += dx;
  }
}
