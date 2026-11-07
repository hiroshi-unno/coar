/* The calls a Juliet socket task makes after Ptr2ArrFC, with glibc's
   types.  socket.ll is written by hand in the form clang 19.1.7 -O0 gives,
   with the locals kept in registers. */
extern int socket(int, int, int);
extern int listen(int, int);
extern int accept(int, void *, void *);
extern int close(int);
extern void reach_error(void);
int main(void) {
  int s = socket(2, 1, 6);
  if (s < -1) reach_error();
  if (listen(s, 5) > 0) reach_error();
  int c = accept(s, 0, 0);
  if (c < -1) reach_error();
  close(c);
  if (close(s) > 0) reach_error();
  return 0;
}
