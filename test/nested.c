#include "benchmarks.h"

int main() {
  NONDET_INT(i);
  int k;
  NONDET_INT(n);
  int l;

  k = 1;
  while (k<n){
    i = 1;
    while (i<n) {
      i++;
    }
    k++;
  }
  assert(1<=k);
 }
