#include "benchmarks.h"

int main() {
  int k;
  NONDET_INT(b);
  int i;
  NONDET_INT(j);
  int n;
  i = j;
  k = 100;
  n = 0;
  while(n < 2*k) {
    if(b) {
      i++;
    } else {
      j++;
    }
    if (b) b = 0; else b = 1;
    n++;
  }
  assert(i == j);
}
