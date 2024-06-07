void fail() {
 ERROR: goto ERROR;
}

int zip(int x, int y) {
  if (x == 0) {
    if (y == 0) {
      return 0;
    } else {
      fail();
    }
  } else if (x >= 0) {
    if (y >= 0) {
      return 1 + zip(x - 1, y - 1);
    } else {
      fail();
    }
  } else {
    fail();
  }
}

int x1, x2;

void unzip(int x) {
  if (x == 0) {
    x1 = 0;
    x2 = 0;
    return;
  } else if (x >= 0) {
    unzip(x - 1);
    x1 = x1 + 1;
    x2 = x2 + 1;
    return;
  } else {
    fail();
  }
}

main() {
  int x;

LOOP:  if (x < 0) goto LOOP;
  unzip(x);
  x = zip(x1, x2);
  printf("%d", x);
}
