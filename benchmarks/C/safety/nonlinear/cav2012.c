/* @require nonlinear invariants
   @from Interpolants as Classifiers
         Rahul Sharma, Aditya V. Nori, and Alex Aiken
         CAV 2012 */

extern error();
extern double nondet_double();
extern int nondet_int();
extern int nondet_bool();
extern double sin(double);
extern double cos(double);

main() {
  double x, y, z;
  do {
    z = nondet_double();
    x = 4 * sin(z) * sin(z);
    y = 4 * cos(z) * cos(z);
  } while (nondet_bool());
  if (x == 2 && y != 2)
    error();
}
