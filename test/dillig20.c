#include "benchmarks.h"

int main()
{
  NONDET_INT(x);
  NONDET_INT(y);
  NONDET_INT(k);
  NONDET_INT(i);
  NONDET_INT(n);
  int j;
  int m;
  m = 0;
  if((x+y) != k)
    return 0;
  j = 0;
  while(j<=n-1) {
    if(j==i)
      {
	x++;
	y--;
      }else
      {
	y++;
	x--;
      }
    if(__nondet_bool())
      m = j;
    j++;
  }
  if(j < n)
    return 0;
  assert(x + y == k);
  assert(n < 1 || m > -1);
  assert(n < 1 || m < n);
}

