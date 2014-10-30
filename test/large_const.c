#include "benchmarks.h"

int main() {
  int c1;
  int c2;
  int c3;
  NONDET_INT(n);
  int v;
  int i, k, j;
  c1 = 4000;
  c2 = 2000;
  c3 = 10000;

  if (n >= 10) return 0;
  if (n < 0) return 0;

  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    v = __nondet_int();
    if (v < 0) return 0;
    if (v >= 2) return 0;
    if( v == 0 )
      k = k + c1;
    else if( v == 1 )
      k = k + c2;
    else
      k = k + c3;
  }

  j = 0;
  while( j < n ) {
    assert(k > 0);
    j++;
    k--;
  }

  return 0;
}
