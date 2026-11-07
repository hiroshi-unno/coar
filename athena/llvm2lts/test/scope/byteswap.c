/* htons (declared const, as glibc does), htonl and inet_addr on constants, as the Juliet socket tasks call
   them (27015 is their port, 127.0.0.1 their address).  byteswap.ll is
   written by hand in the form clang 19.1.7 -O0 gives. */
extern unsigned short htons(unsigned short) __attribute__((__nothrow__, __const__));
extern unsigned int htonl(unsigned int);
extern unsigned int inet_addr(const char *);
extern void reach_error(void);
int main(void) {
  if (htons(27015) != 34665) reach_error();
  if (htonl(0x84030201u) != 0x01020384u) reach_error();
  if (inet_addr("127.0.0.1") != 0x0100007Fu) reach_error();
  return 0;
}
