#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main()
{
  int x = __undef_int();
  int y = __undef_int();

  if (! (x==0)) return 0;
  if (! (y==0)) return 0;

  while (__undef_bool())
    {
      if (__undef_bool())
	{
	  if (! (x >= 9)) return 0;
	  x = x + 2;
	  y = y + 1;
	}
      else
	{
	  if (__undef_bool())
	    {
	      if (!(x >= 7)) return 0;
	      if (!(x <= 9)) return 0;
	      x = x + 1;
	      y = y + 3;
	    }
	  else
	    {
	      if (__undef_bool())
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
