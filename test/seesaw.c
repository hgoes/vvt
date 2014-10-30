#include "benchmarks.h"

int main()
{
  NONDET_INT(x);
  NONDET_INT(y);

  if (! (x==0)) return 0;
  if (! (y==0)) return 0;

  while (__nondet_bool())
    {
      if (__nondet_bool())
	{
	  if (! (x >= 9)) return 0;
	  x = x + 2;
	  y = y + 1;
	}
      else
	{
	  if (__nondet_bool())
	    {
	      if (!(x >= 7)) return 0;
	      if (!(x <= 9)) return 0;
	      x = x + 1;
	      y = y + 3;
	    }
	  else
	    {
	      if (__nondet_bool())
		{
		  if (! (x - 5 >=0)) return 0;
		  if (! (x - 7 <=0)) return 0;
		  x = x + 2;
		  y = y + 1;
		}
	      else
		{
		  if (!(x - 4 <=0)) return 0;
		  x = x + 1;
		  y = y + 2;
		}
	    }
	}
    }
  assert (-x + 2*y  >= 0);
  assert (3*x - y  >= 0);
}
