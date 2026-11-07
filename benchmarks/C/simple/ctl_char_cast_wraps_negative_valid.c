// (char)(x + 1) reduces modulo 256 into -128..127, so from any x in 1..127
// the counter reaches 127 and then wraps to -128: a negative state is
// reachable.  Read as the identity, the cast let x grow forever and EF failed.
// expected: -p cctl valid
int x;
int __phi() { return CEF( CAP(x < 0) ); }
void init() { assume(x > 0); assume(x < 128); }
int body() {
  while(1) {
    x = (char)(x + 1);
  }
}
int main() {}
