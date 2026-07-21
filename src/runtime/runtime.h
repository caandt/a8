#include <sys/syscall.h>
#include <sys/personality.h>
#include <sys/mman.h>
#include <bits/types/siginfo_t.h>
#include <ucontext.h>
#include <signal.h>
#include <fcntl.h>

#define A8_NO_ASLR
#define A8_SEGV_HANDLER
#define A8_POL_HOOK

#define BASE 0x8a8a80000
#define REG(n, val) volatile register long x##n asm("x" #n) = val;
#define REGa(n) REG(n, arg##n)
static inline long syscall1(long num, long arg0) {
  REG(8, num); REGa(0);
  asm volatile ("svc #0" : "+r"(x0) : "r"(x8) : "memory");
  return x0;
}
static inline long syscall2(long num, long arg0, long arg1) {
  REG(8, num); REGa(0); REGa(1);
  asm volatile ("svc #0" : "+r"(x0) : "r"(x1), "r"(x8) : "memory");
  return x0;
}
static inline long syscall3(long num, long arg0, long arg1, long arg2) {
  REG(8, num); REGa(0); REGa(1); REGa(2);
  asm volatile ("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
  return x0;
}
static inline long syscall4(long num, long arg0, long arg1, long arg2, long arg3) {
  REG(8, num); REGa(0); REGa(1); REGa(2); REGa(3);
  asm volatile ("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x3), "r"(x8) : "memory");
  return x0;
}
static inline long syscall6(long num, long arg0, long arg1, long arg2, long arg3, long arg4, long arg5) {
  REG(8, num); REGa(0); REGa(1); REGa(2); REGa(3); REGa(4); REGa(5);
  asm volatile ("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5), "r"(x8) : "memory");
  return x0;
}

#define WRITE(x) syscall3(SYS_write, 1, (long)x, sizeof(x)-1)
#define EXIT(x) do { syscall1(SYS_exit, x); __builtin_unreachable(); } while (0)
#define DIE(x) do { WRITE("a8 runtime: " x "\n"); EXIT(255); } while (0)
#define EXECVE(path, argv, argc) syscall3(SYS_execve, (long)path, argv, argc)
#define PERSONALITY(x) syscall1(SYS_personality, x)
#define MMAP(addr, len) syscall6(SYS_mmap, addr, len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)

static inline void print16(unsigned long val) {
    char buf[16];
    for (int i = 0; i < 16; i++) {
        int shift = (15 - i) * 4;
        int nibble = (val >> shift) & 0xf;
        buf[i] = (nibble < 10) ? ('0' + nibble) : ('a' + (nibble - 10));
    }
    syscall3(SYS_write, 1, (long)buf, 16);
}
static inline void print8(unsigned long val) {
  char buf[8];
  for (int i = 0; i < 8; i++) {
    int shift = (7 - i) * 4;
    int nibble = (val >> shift) & 0xf;
    buf[i] = (nibble < 10) ? ('0' + nibble) : ('a' + (nibble - 10));
  }
  syscall3(SYS_write, 1, (long)buf, 8);
}

#define SA_RESTORER 0x04000000
typedef struct {
  unsigned long sig[1];
} target_sigset_t;
struct kernel_sigaction {
  void (*sigaction)(int, siginfo_t *, void *);
  unsigned long sa_flags;
  void (*restorer)(void);
  target_sigset_t sa_mask;
};
typedef struct {
  unsigned int idx;
  unsigned int dev;
} d_t;
typedef struct {
  unsigned long text_start;
  unsigned long text_end;
  unsigned long new_text_start;
  unsigned long entry;
  unsigned long nrets;
  unsigned long dsize;
  d_t d[];
} rtd_t;

static inline unsigned long lookup(const rtd_t *const rtd, unsigned long addr) {
  unsigned int n = (addr - rtd->text_start) / 4;
  unsigned long low = 0;
  unsigned long high = (long)rtd->dsize - 1;
  unsigned long ans = -1;
  while (low <= high) {
    unsigned long mid = low + (high - low) / 2;
    if (rtd->d[mid].idx < n) {
      ans = mid;
      low = mid + 1;
    } else {
      high = mid - 1;
    }
  }
  if (ans == -1) {
    return rtd->new_text_start + (4 * n);
  }
  return rtd->new_text_start + (4 * (n + rtd->d[ans].dev));
}
#define MAP_HEADER_MAGIC 0x7963696c6f70a8a8
typedef struct {
  unsigned long magic;
  unsigned long nrets;
  unsigned long nextfree;
} map_header;
typedef struct {
  unsigned long vals[8];
  unsigned long nextoffset;
} map_entry;
