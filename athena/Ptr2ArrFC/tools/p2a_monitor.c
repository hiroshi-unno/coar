/* Runtime of the region monitor (ptr2arr --monitor).

   p2a_mon_reg records an object instance: its address range and the region
   the analysis put it in. p2a_mon_chk, called before a dereference, finds the
   latest registration containing the address and compares its region with
   the region the analysis gives the dereferenced pointer. A mismatch is
   reported on stderr as P2A_REGION_VIOLATION and ends the run with status 79;
   an address no registration contains is counted, and the count is reported
   at exit as P2A_REGION_UNKNOWN when it is not zero.

   p2a_mon_heap registers a block from malloc or calloc as a heap block, and
   p2a_mon_free, called before free, marks the latest heap block starting at
   its argument released. p2a_mon_end, called at an end of the execution
   (through atexit, registered by p2a_mon_start at the start of main, or
   right before a call that ends the execution without the atexit
   functions), reports the heap blocks not released as P2A_HEAP_LEFT, once. */
#include <stdio.h>
#include <stdlib.h>

struct p2a_mon_entry { const char *lo; unsigned long n; int rid; int heap; int freed; };
static struct p2a_mon_entry *p2a_mon_tab;
static unsigned long p2a_mon_len, p2a_mon_cap, p2a_mon_unknown, p2a_mon_checks;

static void p2a_mon_report(void) {
  fprintf(stderr, "P2A_REGION_CHECKS %lu\n", p2a_mon_checks);
  if (p2a_mon_unknown) fprintf(stderr, "P2A_REGION_UNKNOWN %lu\n", p2a_mon_unknown);
}

void p2a_mon_reg(void *p, unsigned long n, int rid) {
  if (p2a_mon_cap == 0) atexit(p2a_mon_report);
  if (p2a_mon_len == p2a_mon_cap) {
    p2a_mon_cap = p2a_mon_cap ? 2 * p2a_mon_cap : 256;
    p2a_mon_tab = realloc(p2a_mon_tab, p2a_mon_cap * sizeof *p2a_mon_tab);
    if (!p2a_mon_tab) abort();
  }
  p2a_mon_tab[p2a_mon_len].lo = p;
  p2a_mon_tab[p2a_mon_len].n = n ? n : 1;
  p2a_mon_tab[p2a_mon_len].rid = rid;
  p2a_mon_tab[p2a_mon_len].heap = 0;
  p2a_mon_tab[p2a_mon_len].freed = 0;
  p2a_mon_len++;
}

void p2a_mon_heap(void *p, unsigned long n, int rid) {
  if (!p) return; /* realloc(p, 0) */
  p2a_mon_reg(p, n, rid);
  p2a_mon_tab[p2a_mon_len - 1].heap = 1;
}

void p2a_mon_free(void *p) {
  unsigned long i = p2a_mon_len;
  if (!p) return;
  while (i > 0) {
    struct p2a_mon_entry *e = &p2a_mon_tab[--i];
    if (e->heap && e->lo == (const char *)p && !e->freed) {
      e->freed = 1;
      return;
    }
  }
}

void p2a_mon_end(void) {
  static int done;
  unsigned long i, left = 0;
  if (done) return;
  done = 1;
  for (i = 0; i < p2a_mon_len; i++)
    if (p2a_mon_tab[i].heap && !p2a_mon_tab[i].freed) left++;
  fprintf(stderr, "P2A_HEAP_LEFT %lu\n", left);
}

void p2a_mon_start(void) { atexit(p2a_mon_end); }

void p2a_mon_chk(void *p, int rid, int line) {
  const char *a = p;
  unsigned long i = p2a_mon_len;
  p2a_mon_checks++;
  while (i > 0) {
    struct p2a_mon_entry *e = &p2a_mon_tab[--i];
    if (a >= e->lo && a < e->lo + e->n) {
      if (e->rid != rid) {
        fflush(stdout);
        fprintf(stderr, "P2A_REGION_VIOLATION line %d: a pointer of region %d reached an object of region %d\n",
                line, rid, e->rid);
        _Exit(79);
      }
      return;
    }
  }
  p2a_mon_unknown++;
}
