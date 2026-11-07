// continue goes to the next iteration, so y = 2 never runs and y stays at most 1.
// expected: -p cctl valid
int y;
int __phi() { return CAG( CAP(y <= 1) ); }
void init() { y = 0; }
int body() {
  while(1) { y = 1; continue; y = 2; }
}
int main() {}
