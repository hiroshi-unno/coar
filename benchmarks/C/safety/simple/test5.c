struct pair {
  int fst;
  int snd;
};

struct pair cons(int fst, int snd) {
  struct pair p;
  p.fst = fst;
  p.snd = snd;
  return p;
}

main() {
  struct pair p = cons(29, 13);
  return p.fst + p.snd;
}
