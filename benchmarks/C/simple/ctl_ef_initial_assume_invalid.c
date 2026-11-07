// EF is asked of every initial state that init() allows.  From x = 1 the
// value only decreases, so x > 5 is never reached: the property fails.
int x;
int __phi() { return CEF( CAP(x > 5) ); }
void init() { assume(x > 0); }
int body() {
  while(1) {
    x = x - 1;
  }
}
int main() {}
