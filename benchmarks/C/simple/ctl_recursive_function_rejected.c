// A recursive helper is refused: calls are inlined, and unfolding a recursive
// one does not terminate.
// expected: -p cctl refused (semantic error)
int y;
int __phi() { return CAF( CAP(y == 6) ); }
void init() { y = 0; }
int r;
int fact(int n) { if (n <= 1) { return 1; } r = fact(n - 1); return n * r; }
int body() {
  y = fact(3);
  while(1) { }
}
int main() {}
