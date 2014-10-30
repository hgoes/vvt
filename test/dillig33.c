#include "benchmarks.h"

int main()
{
  NONDET_INT(k);
  int z;
  int x;
  int y;
  int c;
  z = k;
  x = y = 0;

  while(__nondet_bool())
  {
    c = 0;
    while(__nondet_bool())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
    while(__nondet_bool())
    {
      x--;
      y--;
    }
    z=k+y;
  }
  assert(x == y);
}
