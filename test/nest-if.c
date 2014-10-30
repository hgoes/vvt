#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int i,k;

  k = 1;
  while (k<n){
    i = 1;
    while (i<n) {
      assert(1<=k);
      i++;
    }
    if(i<n) {
      i = 1;
      while (i<n) { i++; }
    }
    k++;
  }

 }
