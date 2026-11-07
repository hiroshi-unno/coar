/* Strong definitions of the functions an --uninit=nondet output draws the
   starting values of its uninitialised variables from: each returns zero
   and draws nothing, in place of the output's weak definitions, which
   return __VERIFIER_nondet_k(). A run of the output linked with this file
   reads zero where the input, compiled to start its automatic variables at
   zero, reads its uninitialised memory, and makes the same nondeterministic
   draws.

   The output may have renamed the functions (when the input uses the
   names); compile this file with -DP2A_UNINIT_<kind>=<name> for each
   function the record lists in uninit_generators. A kind whose name is not
   given is not defined. With -DP2A_UNINIT_WIDE the integer kinds other
   than bool return __int128, as in the output of ptr2arr --z-reading. */

#ifdef P2A_UNINIT_WIDE
#define P2A_INT(t) __int128
#else
#define P2A_INT(t) t
#endif

#ifdef P2A_UNINIT_bool
_Bool P2A_UNINIT_bool(void) { return 0; }
#endif

#ifdef P2A_UNINIT_char
P2A_INT(char) P2A_UNINIT_char(void) { return 0; }
#endif

#ifdef P2A_UNINIT_schar
P2A_INT(signed char) P2A_UNINIT_schar(void) { return 0; }
#endif

#ifdef P2A_UNINIT_uchar
P2A_INT(unsigned char) P2A_UNINIT_uchar(void) { return 0; }
#endif

#ifdef P2A_UNINIT_short
P2A_INT(short) P2A_UNINIT_short(void) { return 0; }
#endif

#ifdef P2A_UNINIT_ushort
P2A_INT(unsigned short) P2A_UNINIT_ushort(void) { return 0; }
#endif

#ifdef P2A_UNINIT_int
P2A_INT(int) P2A_UNINIT_int(void) { return 0; }
#endif

#ifdef P2A_UNINIT_uint
P2A_INT(unsigned int) P2A_UNINIT_uint(void) { return 0; }
#endif

#ifdef P2A_UNINIT_long
P2A_INT(long) P2A_UNINIT_long(void) { return 0; }
#endif

#ifdef P2A_UNINIT_ulong
P2A_INT(unsigned long) P2A_UNINIT_ulong(void) { return 0; }
#endif

#ifdef P2A_UNINIT_longlong
P2A_INT(long long) P2A_UNINIT_longlong(void) { return 0; }
#endif

#ifdef P2A_UNINIT_ulonglong
P2A_INT(unsigned long long) P2A_UNINIT_ulonglong(void) { return 0; }
#endif

#ifdef P2A_UNINIT_float
float P2A_UNINIT_float(void) { return 0; }
#endif

#ifdef P2A_UNINIT_double
double P2A_UNINIT_double(void) { return 0; }
#endif
