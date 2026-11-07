// f's parameter x is not the global x: the global stays 0.
int x;
int __phi() { return CAG( CAP(x == 0) ); }
void init() { x = 0; }
void f(int x) { x = x + 1; }
int body() {
  while(1) {
    f(5);
  }
}
int main() {}
