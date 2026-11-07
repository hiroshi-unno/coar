// EF from every initial state with x > 0: x then grows past 5.  A state with
// x <= 0 would stay put and fail, so the assumption in init() must guard the
// property.
int x;
int __phi() { return CEF( CAP(x > 5) ); }
void init() { assume(x > 0); }
int body() {
  while(1) {
    if (x > 0) { x = x + 1; }
  }
}
int main() {}
