struct pair1 {
  int fst;
  struct pair2 {
    int snd;
    int trd;
  } next;
};

struct pair1 cons(int fst, int snd, int trd) {
  struct pair1 p;
  p.fst = fst;
  p.next.snd = snd;
  p.next.trd = trd;
  return p;
}

main() {
  struct pair1 p = cons(18, 15, 9);
  return p.fst + p.next.snd + p.next.trd;
}