/* p2a-expect: normal=0 memory-safety=0 memory-safety+reach-error=0 memory-cleanup=0 assume-safety=0 */
/* Constants that fold to infinities: the transformation folds them, and
   the printer would write inff and inf; the output writes them as
   divisions by zero, which a compiler folds to the same values. */
static const float pinf = 1.0f / 0.0f;
static const double ninf = -1.0 / 0.0;
static const long double linf = 1.0L / 0.0L;
int main(void) {
  float x = pinf;
  double y = ninf;
  long double z = linf;
  if (!(x > 1e30f)) return 1;
  if (!(y < -1e300)) return 2;
  if (!(z > 1e300L)) return 3;
  if (x - x == x - x || y - y == y - y) return 4;
  return 0;
}
