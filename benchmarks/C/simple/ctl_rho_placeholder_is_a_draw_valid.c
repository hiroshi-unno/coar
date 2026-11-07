// An undeclared, never-assigned __rho_<k>_ name is a nondeterministic choice
// made at each read (Cook and Koskinen, PLDI 2013, Section 5.2: the encoding
// introduces rho := * before every choice).  Every iteration may take the
// branch, so x = 1 is reachable from every initial state.  Read as one value
// fixed by the initial state, a state with __rho_1_ <= 0 never takes it.
int x;
int __phi() { return CEF( CAP(x == 1) ); }
void init() { x = 0; }
int body() {
  while(1) {
    if (__rho_1_ > 0) { x = 1; }
  }
}
int main() {}
