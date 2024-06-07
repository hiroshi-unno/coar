int sum(int x) {
  if(x > 0) {
    return x + sum(x - 1);
  } else {
    return 0;
  }
}

main() {
  int y = sum(9) - 3;
  return y;
}
