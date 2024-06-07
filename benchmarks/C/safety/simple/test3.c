main() {
  int x = 0;
  int n = 42;
L:
  if (x < n) {
    x = x + 1;
    goto L;
  }
  return x;
}
