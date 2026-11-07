// LIMIT is 5 in the property as in the body: x stays at most 5.
#define LIMIT 5
int x;
int __phi() { return CAG( CAP(x <= LIMIT) ); }
void init() { x = 0; }
int body() {
  while(1) {
    if (x < LIMIT) { x = x + 1; }
  }
}
int main() {}
