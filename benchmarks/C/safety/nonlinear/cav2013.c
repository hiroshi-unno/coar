/* @require nonlinear invariants
   @from Generating Non-Linear Interpolants by Semidefinite Programming
         Liyun Dai, Bican Xia, and Naijun Zhan
         CAV 2013 */

extern error();

main() {
  double x, y, z;
  if (x * x + y * y < 1)
    while (x * x + y * y < 3) {
      x = x * x + y - 1;
      y = y + x * y + 1;
      if (x * x - 2 * y * y - 4 > 0)
        error();
    }
}
