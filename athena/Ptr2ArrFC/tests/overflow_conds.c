/* The check functions of ptr2arr --check-overflow against a reference.
   tests/overflow_conds.sh transforms tests/overflow_conds_ops.c, which uses
   every checked operation at int, long and long long, and compiles the
   output's check functions (with main renamed away) with this file. Each
   check calls reach_error() exactly when the exact result is out of range;
   the reference is gcc's __builtin_*_overflow, the INT_MIN / -1 case, and
   for a left shift the product a * 2^b. Every pair of a set of edge values
   is tried, then random pairs. Prints the number of disagreements per
   function and "checked N" ; exit status 1 on any disagreement. */
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

static int reported;
void reach_error(void) { reported = 1; }
/* the draws of the transformed main, which is never called */
int __VERIFIER_nondet_int(void) { return 0; }
long long __VERIFIER_nondet_longlong(void) { return 0; }

void __p2a_overflow_add_s32(int, int);
void __p2a_overflow_sub_s32(int, int);
void __p2a_overflow_mul_s32(int, int);
void __p2a_overflow_neg_s32(int);
void __p2a_overflow_div_s32(int, int);
void __p2a_overflow_shl_s32_s32(int, int);
void __p2a_overflow_add_s64(long long, long long);
void __p2a_overflow_sub_s64(long long, long long);
void __p2a_overflow_mul_s64(long long, long long);
void __p2a_overflow_neg_s64(long long);
void __p2a_overflow_div_s64(long long, long long);
void __p2a_overflow_shl_s64_s32(long long, int);

static unsigned long long state = 88172645463325252ULL;
static unsigned long long next(void) {
  state ^= state << 13; state ^= state >> 7; state ^= state << 17;
  return state;
}

static long long edges[200];
static int nedges;
static void edge_values(int w) {
  long long max = w == 64 ? LLONG_MAX : INT_MAX, min = w == 64 ? LLONG_MIN : INT_MIN;
  long long base[] = { 0, 1, -1, 2, -2, 3, -3, max, max - 1, max - 2, min, min + 1, min + 2,
                       max / 2, max / 2 + 1, min / 2, min / 2 - 1, max / 3, min / 3 };
  nedges = 0;
  for (unsigned i = 0; i < sizeof base / sizeof *base; i++) edges[nedges++] = base[i];
  for (int k = 1; k < w - 1; k += 3) {
    long long p = 1LL << k;
    edges[nedges++] = p; edges[nedges++] = -p; edges[nedges++] = p + 1; edges[nedges++] = -p - 1;
  }
}

static long long rnd(int w) {
  long long v = (long long)next();
  switch (next() % 4) {
  case 0: return w == 64 ? v : (int)v;
  case 1: return v % 70000;
  case 2: return edges[next() % nedges] + (long long)(next() % 5) - 2;
  default: return w == 64 ? v >> (next() % 63) : (int)(v >> (next() % 63));
  }
}

static int fits(long long v, int w) { return w == 64 || (v >= INT_MIN && v <= INT_MAX); }

/* the reference: is the exact result of op on (a, b) at width w out of range? */
static int ref(int op, long long a, long long b, int w) {
  long long r;
  switch (op) {
  case 0: return w == 64 ? __builtin_add_overflow(a, b, &r) : !fits(a + b, 32);
  case 1: return w == 64 ? __builtin_sub_overflow(a, b, &r) : !fits(a - b, 32);
  case 2: return w == 64 ? __builtin_mul_overflow(a, b, &r) : !fits(a * b, 32);
  case 3: return a == (w == 64 ? LLONG_MIN : INT_MIN);
  case 4: return a == (w == 64 ? LLONG_MIN : INT_MIN) && b == -1;
  default:
    if (b < 0 || b >= w) return 0;
    if (b == 63) return !(a == 0 || a == -1);
    if (w == 64) return __builtin_mul_overflow(a, 1LL << b, &r);
    return !fits(a * (1LL << b), 32);
  }
}

static void call(int op, long long a, long long b, int w) {
  reported = 0;
  if (w == 32) {
    switch (op) {
    case 0: __p2a_overflow_add_s32((int)a, (int)b); break;
    case 1: __p2a_overflow_sub_s32((int)a, (int)b); break;
    case 2: __p2a_overflow_mul_s32((int)a, (int)b); break;
    case 3: __p2a_overflow_neg_s32((int)a); break;
    case 4: if (b != 0) __p2a_overflow_div_s32((int)a, (int)b); break;
    default: __p2a_overflow_shl_s32_s32((int)a, (int)b);
    }
  } else {
    switch (op) {
    case 0: __p2a_overflow_add_s64(a, b); break;
    case 1: __p2a_overflow_sub_s64(a, b); break;
    case 2: __p2a_overflow_mul_s64(a, b); break;
    case 3: __p2a_overflow_neg_s64(a); break;
    case 4: if (b != 0) __p2a_overflow_div_s64(a, b); break;
    default: __p2a_overflow_shl_s64_s32(a, (int)b);
    }
  }
}

int main(void) {
  static const char *names[] = { "add", "sub", "mul", "neg", "div", "shl" };
  long long checked = 0, bad = 0;
  for (int w = 32; w <= 64; w += 32) {
    edge_values(w);
    for (int op = 0; op < 6; op++) {
      long long d = 0;
      for (int pass = 0; pass < 2; pass++) {
        long long n = pass == 0 ? (long long)nedges * nedges : 2000000;
        for (long long i = 0; i < n; i++) {
          long long a, b;
          if (pass == 0) { a = edges[i / nedges]; b = edges[i % nedges]; }
          else { a = rnd(w); b = rnd(w); }
          if (op == 5) b = pass == 0 ? (i % (w + 3)) - 1 : (long long)(next() % (w + 4)) - 2;
          if (op == 4 && b == 0) continue;
          /* the operands of an operation of type int are ints */
          if (!fits(a, w) || (op != 5 && !fits(b, w))) continue;
          call(op, a, b, w);
          checked++;
          if (reported != ref(op, a, b, w)) {
            if (d < 3) fprintf(stderr, "%s_s%d(%lld, %lld): check %d, reference %d\n",
                               names[op], w, a, b, reported, ref(op, a, b, w));
            d++;
          }
        }
      }
      printf("%s_s%d disagreements %lld\n", names[op], w, d);
      bad += d;
    }
  }
  printf("checked %lld\n", checked);
  return bad != 0;
}
