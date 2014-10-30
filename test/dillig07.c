#include "benchmarks.h"

int main()
{
  NONDET_INT(n);
  int i, j;
  i = j = 0;
  if(!(n >= 0)) return 0;
  while(i<n) {
    i++;
    j++;
  }	
  assert(j < n+1);
}

