#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

//This example is adapted from StInG 
int main()
{
  int x1 = __undef_int();
  int x2 = __undef_int();
  int x3 = __undef_int();
  int x4 = __undef_int();
  int x5 = __undef_int();
  int x6 = __undef_int();

  if (! (x1>=1)) return 0;
  if (! (x2==0)) return 0;
  if (! (x3==0)) return 0;
  if (! (x4==1)) return 0;
  if (! (x5==0)) return 0;
  if (! (x6==0)) return 0;
  
  while(__undef_bool())
    {
      if (__undef_bool())
	{
	  if (! (x1 >= 1)) return 0;
	  if (! (x4 >= 1)) return 0;
	  x1=x1-1;
	  x4=x4-1;
	  x2=x2+1;
	  x5=x5+1;
	}
      else
	{
	  if (__undef_bool())
	    {
	      if (! (x2 >= 1)) return 0;
	      if (! (x6 >= 1)) return 0;
	      x2=x2-1;
	      x3=x3+1;
	    }
	  else
	    {
	      if (__undef_bool())
		{
		  if (! (x4 >= 1)) return 0;
		  if (! (x3 >= 1)) return 0;
		  x3=x3-1;
		  x2=x2+1;
		}
	      else
		{
		  if (__undef_bool())
		    {
		      if (! (x3>=1)) return 0;
		      x3=x3-1;
		      x1=x1+1;
		      x6=x6+x5;
		      x5=0;
		    }
		  else
		    {
		      if (! (x2 >= 1)) return 0;
		      x2 = x2 - 1;
		      x1 = x1 + 1;
		      x4 = x4 + x6;
		      x6 = 0;
		    }
		}
	    }
	}
    }
  
  assert (x4 + x5 + x6 -1 >= 0); 
  assert (x4 + x5 + x6 -1 <= 0); 
  assert (x4 + x5 <= 1);
  assert (x5  >= 0);
  assert (x4  >= 0);
  assert (x3  >= 0);
  assert (x2  >= 0);
  assert (x1 + x5 >= 1);
  assert (x1 + x2 >= x4 + x5);
  assert (x1 + x2 + x3 >= 1);
  
}

