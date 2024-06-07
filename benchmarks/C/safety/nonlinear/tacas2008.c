/* @require nonlinear invariants
   @from Automatically Refining Abstract Interpretations
         Bhargav S. Gulavani, Supratik Chakraborty, Aditya V. Nori, and Sriram K. Rajamani
         TACAS 2008
   @used Generating Non-Linear Interpolants by Semidefinite Programming
         Liyun Dai, Bican Xia, and Naijun Zhan
         CAV 2013 */

extern error();
extern double nondet_double();
extern int nondet_int();
extern int nondet_bool();

assert(int b) {
  if (!b) {
    error();
  }
}

main() {
  int x, y;
  int xa = 0;
  int ya = 0;
  while (nondet_bool()) {
    x = xa + 2 * ya;
    y = -2 * xa + ya;
    x ++;
    if (nondet_bool()) y = y + x;
    else y = y - x;
    xa = x - 2 * y;
    ya = 2 * x + y;
  }
  assert (xa + 2 * ya >= 0);
}
