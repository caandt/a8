#include <syscall.h>
#define MSG "\n*** cfi abort ***\n"

asm("_start: b abort");

long syscall(long num, long arg1, long arg2, long arg3) {
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
  syscall(SYS_write, 1, (long)MSG, sizeof(MSG)-1);
  syscall(SYS_exit, 255, 0, 0);
}

