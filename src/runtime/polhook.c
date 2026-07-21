#include "runtime.h"
#ifdef A8_POL_HOOK
asm(R"(
.global log_b_prologue
log_b_prologue:
  add x1, sp, #16
  b log_b
log_b_epilogue:
  ldp x0, x1, [sp], #16
  ret
)");
void log_b_epilogue();
void add(unsigned long, unsigned long);
void log_b(unsigned long src, unsigned long *dst) {
  rtd_t *rtd; asm("adrp %0, 0\nldr %0, [%0, #12]" : "=r"(rtd));
  long d = *dst;
  if (d < rtd->text_end && rtd->text_start < d)
    d = lookup(rtd, d);
  add(src, d);
  *dst = d;
  return log_b_epilogue();
}
void add(unsigned long key, unsigned long val) {
  map_header *header = (map_header*)BASE;
  if (header->nrets <= key) DIE("Invalid polhook key");
  map_entry *e = ((map_entry*)(BASE + sizeof(map_header))) + key;
  while (1) {
    for (int i = 0; i < 7; i++) {
      if (e->vals[i] == 0) {
        e->vals[i] = val;
        return;
      } else if (e->vals[i] == val) {
        return;
      }
    }
    if (e->nextoffset == 0) {
      e->nextoffset = header->nextfree;
      *(unsigned long*)(BASE + header->nextfree) = val;
      header->nextfree += sizeof(map_entry);
      return;
    }
    e = (void*)(BASE + e->nextoffset);
  }
}
#else
void log_b_prologue(){
    DIE("no pol hook");
}
#endif
