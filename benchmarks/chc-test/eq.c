void f(int x, int y) {
  // {x = x_init /\ y = 0}
  while (x != 0) {
    y = y + 1;
    x = x - 1;
  }
  // {y = x_init}
}
