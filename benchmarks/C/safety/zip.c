void fail() {
 ERROR: goto ERROR;
}

int zip(int x, int y) {
  int res = 0;
  while (1) {
    if (x == 0) {
      if (y == 0) {
	break;
      } else {
	fail();
      }
    } else if (x >= 0) {
      if (y >= 0) {
	res = res + 1;
	x = x - 1;
	y = y - 1;
      } else {
	fail();
      }
    } else {
      fail();
    }
  }
  return res;
}

main() {
  int res1 = 0;
  int res2 = 0;
  int x;

LOOP:  if (x < 0) goto LOOP;
  while (1) {
    if (x == 0) {
      break;
    } else if (x >= 0) {
      res1 = res1 + 1;
      res2 = res2 + 1;
      x = x - 1;
    } else {
      fail();
    }
  }
  return zip(res1, res2);
}
