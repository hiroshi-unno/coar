/* Forms that stay refused: a function pointer given to an external
   function. (An ordered comparison of function pointers is refused by the
   front end itself, as invalid input.) */
extern void register_handler(void (*)(int));
static void h(int x) { (void)x; }
int main(void) {
  register_handler(h);
  return 0;
}
