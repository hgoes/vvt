#include "benchmarks.h"

int main() {
  NONDET_INT(n);
  int i,k,l;

  k = 1;
  while (k<n){
    assert(1<=k);
    i = 1;
    i = 1; while (i < n) i++;  
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    i = 1; while (i < n) i++;
    k++;
  }

 }
