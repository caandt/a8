#include <sys/syscall.h>
#include <sys/personality.h>

#define WRITE(x) syscall(SYS_write, 1, (long)x, sizeof(x)-1)
#define EXIT(x) syscall(SYS_exit, x, 0, 0)
#define DIE(x) do { WRITE("a8 runtime: " x "\n"); EXIT(255); } while (0)
#define EXECVE(path, argv, argc) syscall(SYS_execve, (long)path, argv, argc)
#define PERSONALITY(x) syscall(SYS_personality, x, 0, 0)

asm("b abort\n"
    "b _start\n"
    "real_entry: .fill 8\n"
    "_start:\n"
    "add x0, sp, #8\n"
    "ldr x1, [sp]\n"
    "add x1, x0, x1, lsl #3\n"
    "add x1, x1, #8\n"
    "bl disable_aslr\n"
    "mov lr, #0\n"
    "ldr x19, real_entry\n"
    "br x19\n");

inline long syscall(long num, long arg1, long arg2, long arg3) {
  register long x8 asm("x8") = num;
  register long x0 asm("x0") = arg1;
  register long x1 asm("x1") = arg2;
  register long x2 asm("x2") = arg3;

  asm volatile (
    "svc #0"
    : "+r"(x0)
    : "r"(x1), "r"(x2), "r"(x8)
    : "memory"
  );

  return x0;
}

void abort() {
  DIE("CFI abort");
}

void disable_aslr(long argv, long envp) {
  long p1 = PERSONALITY(0xffffffff);
  long p2 = p1 | ADDR_NO_RANDOMIZE;
  if (p1 != p2) {
    if (PERSONALITY(p2) == -1) {
      DIE("Could not change personality");
    }
    EXECVE("/proc/self/exe", argv, envp);
    DIE("Could not re-exec program");
  }
}
