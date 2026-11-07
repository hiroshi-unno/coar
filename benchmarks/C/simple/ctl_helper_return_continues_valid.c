// return 1; leaves one(), not the program: y becomes 1, then 2.
int y;
int __phi() { return CAF( CAP(y == 2) ); }
void init() { y = 0; }
int one() { return 1; }
int body() {
  y = one();
  y = y + 1;
  while(1) { }
}
int main() {}
