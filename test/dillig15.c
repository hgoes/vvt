#include "benchmarks.h"

int main() {

  NONDET_INT(n);
  int i;
  NONDET_INT(k);
  int j;
  if(n < 1)
    return 0;
  if(k < n)
    return 0;
  j = 0;
  while( j <= n-1 ) {
    j++;
    k--;
  } 
  if(j < n)
    return 0;
  assert(k > -1);
}
