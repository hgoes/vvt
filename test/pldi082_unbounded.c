#include "benchmarks.h"

int main(){

  int x;
  int y;
  NONDET_INT(n);
  x = y = 0;

  if(n < 0)
    return 1;

  while (1){
     if (x <= n)
        y++;
     else if(x >= n+1)
       y--;
     else return 1;

     if ( y < 0)
       break;
     x++;
  }

  if(n >= 0)
    if(y == -1)
      if (x >= 2 * n + 3)
        assert(0);
}

