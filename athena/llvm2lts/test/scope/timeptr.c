/* time with an argument other than NULL writes through it: refused. */
typedef long time_t;
extern time_t time(time_t *);
int main(void) {
  time_t t;
  time(&t);
  return 0;
}
