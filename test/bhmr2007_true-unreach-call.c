#include "benchmarks.h"
int main() {
  int i, a, b;
  i = 0; a = 0; b = 0;
  NONDET_INT(n);
  if (!(n >= 0)) return 0;
  while (i < n) {
    if (__nondet_bool()) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  assert(a + b == 3*n);
  return 0;
}
