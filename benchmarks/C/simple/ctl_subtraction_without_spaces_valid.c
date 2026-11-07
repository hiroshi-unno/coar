// x-1 is a subtraction: x only decreases from 0.
int x;
int __phi() { return CAG( CAP(x <= 0) ); }
void init() { x = 0; }
int body() {
  while(1) {
    x = x-1;
  }
}
int main() {}
