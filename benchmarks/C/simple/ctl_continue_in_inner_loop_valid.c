// A continue in the inner loop goes back to that loop's head, whose break then
// leaves it; y = 2 never runs.
// expected: -p cctl valid
int y; int x;
int __phi() { return CAG( CAP(y <= 1) ); }
void init() { y = 0; x = 0; }
int body() {
  while(1) { x = 0; while(1) { if (x == 1) { break; } x = 1; y = 1; continue; y = 2; } }
}
int main() {}
