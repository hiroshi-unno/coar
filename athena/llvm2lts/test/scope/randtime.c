/* srand(time(NULL)) and rand(), as the Juliet tasks seed and draw, with
   glibc's declarations (__leaf__ read as nocallback). */
typedef long time_t;
extern int rand(void) __attribute__((__nothrow__, __leaf__));
extern void srand(unsigned int) __attribute__((__nothrow__, __leaf__));
extern time_t time(time_t *) __attribute__((__nothrow__, __leaf__));
extern void reach_error(void);
int main(void) {
  srand((unsigned int)time((time_t *)0));
  int r = rand();
  if (r < 0) reach_error();
  return 0;
}
