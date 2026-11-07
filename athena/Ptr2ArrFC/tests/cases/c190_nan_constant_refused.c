/* Expected: refused (exit status 2), kind float-constant. A constant that
   folds to a NaN: Frama-C folds 0.0f * (1.0f / 0.0f) to a NaN of the other
   sign than GCC's, which signbit, copysign and the bits can see. */
static const float nan_value = 0.0f * (1.0f / 0.0f);
int main(void) {
  float x = nan_value;
  return x == x;
}
