// The draw overwrites x = 1: x is any value initially, so AG(x == 1) fails.
int x;
int __phi() { return CAG( CAP(x == 1) ); }
void init() { x = 1; x = nondet(); }
int body() {
  while(1) { }
}
int main() {}
