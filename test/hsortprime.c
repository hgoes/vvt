#include "benchmarks.h"

//This example is adapted from StInG 
int main()
{
  NONDET_INT(n);
  NONDET_INT(l);
  NONDET_INT(r);
  NONDET_INT(i);
  NONDET_INT(j);

  if (! (n >= 2)) return 0;
  if (! (r - n == 0)) return 0;
  if (! (i - l ==0)) return 0;
  if (! (j - 2*l == 0)) return 0;
  if (! (2*l - n >= 0)) return 0;
  if (! (2*l - n - 1 <= 0)) return 0;

  while (__nondet_bool())
    {
      if (__nondet_bool())
	{
	  if (! (r -j  -1 >= 0)) return 0;
	  i = j + 1;
	  j = 2*j + 2;
	}
      else
	{
	  if (__nondet_bool())
	    {
	      if (! (j -r <=0)) return 0;
	      i = j;
	      j = 2*j;
	    }
	  else
	    {
	      if (__nondet_bool())
		{
		  if (! (l >=2)) return 0;
		  if (! (r  >=2)) return 0;
		  i = l - 1;
		  j = 2 *l - 2;
		  l = l - 1;
		}
	      else
		{
		  if (! (l <= 1)) return 0;
		  r = r - 1;
		  if (! (r >=3)) return 0;
		  i = l;
		  j = 2*l;
		}
	    }
	}
    }
  assert (-2*l + r + 1 >= 0);
  return 0;
}

// LI computed is
// 2*i - j = 0 &&
// -2*l + r >= -1 &&
// -2*l + 3*r - 2*i >= 0 && 
// -l + i >= 0 && 
// r >= 2 &&
// l >= 1 &&
// n - r >= 0
