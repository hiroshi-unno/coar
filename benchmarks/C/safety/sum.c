int sum(int x) {
  if (x <= 0) {
    return 0;
  } else {
    return x + sum(x - 1);
  }
}
main() {
  int x;
  if (sum(x) >= x) {
    return;
  } else {
  ERROR:
    return;
  }
}
