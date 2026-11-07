// !x > 0 is (!x) > 0: with x = -1, !x is 0 and the branch is never taken.
int x;
int __phi() { return CAG( CAP(x == -1) ); }
void init() { x = -1; }
int body() {
  while(1) {
    if (!x > 0) { x = 5; }
  }
}
int main() {}
