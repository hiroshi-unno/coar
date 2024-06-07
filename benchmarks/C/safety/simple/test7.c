main() {
  int mul = 0;
  int x = 0;
  int n = 7;
  int m = 6;
  while (x < n) {
    int y = 0;
    while (y < m) {
      y = y + 1;
      mul = mul + 1;
    }
    x = x + 1;
  }
  return mul;
}
