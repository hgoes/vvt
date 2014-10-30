#include "benchmarks.h"

int main()
{
  NONDET_BOOL(flag);
  int x;
  int y;
  int j;
  int i;
  
  x = y = j = i = 0;
  
  while(__nondet_bool())
    {
      x++;
      y++;
      i=i+x;
      j=j+y;
      if(flag)  j=j+1;
    } 
  assert(j > i - 1);
}
