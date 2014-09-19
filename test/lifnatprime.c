#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

//This example is adapted from StinG 
int main()
{
  int i = __undef_int();
  int sa;
  int ea;
  int ma;
  int sb;
  int eb;
  int mb;
  
  if (! (i>=1)) return 0;
  sa=0;
  ea=0;
  ma=0;
  sb=0;
  eb=0;
  mb=0;
  
  while(__undef_bool())
    {
      if (__undef_bool())
	{
	  if (! (eb >=1)) return 0;
	  eb = eb -1;
	  mb = mb +1;
	}
      else
	{
	  if (__undef_bool())
	    {
	      if (! (ea >=1)) return 0;
	      ea = ea -1;
	      ma = ma +1;
	    }
	  else
	    {
	      if (__undef_bool())
		{
		  if (! (sa>=1)) return 0;
		  sa=sa-1;
		  i=i+sb+eb+mb;
		  sb=0;
		  eb=1;
		  mb=0;
		  
		}
	      else
		{
		  if (__undef_bool())
		    {
		      if (! (sb>=1)) return 0;
		      i=i+sb+eb+mb;
		      sb=0;
		      eb=1;
		      mb=0;
		    }
		  else
		    {
		      if (__undef_bool())
			{
			  
			  if (! (sb>=1)) return 0;
			  sb=sb-1;
			  i=i+sa+ea+ma;
			  sa=0;
			  ea=1;
			  ma=0;
			  
			}
		      else
			{
			  if (__undef_bool())
			    {
			      if (! (sa>=1)) return 0;
			      i=i+sa+ea+ma;
			      sa=0;
			      ea=1;
			      ma=0;
			    }
			  else
			    {
			      if (__undef_bool())
				{
				  if (! (sa>=1)) return 0;
				  sa=sa-1;
				  sb=sb+eb+mb+1;
				  eb=0;
				  mb=0;
				}
			      else
				{
				  if (__undef_bool())
				    {
				      if (! (i>=1)) return 0;
				      i=i-1;
				      sb=sb+eb+mb+1;
				      eb=0;
				      mb=0;
				    }
				  else
				    {
				      if (__undef_bool())
					{
					  if (! (i >= 1)) return 0;
					  i = i -1;
					  sa = sa + ea + ma + 1;
					  ea = 0;
					  ma =0;
					}
				      else
					{
					  if (! (sb >= 1)) return 0;
					  sb = sb-1;
					  sa = ea+ma+1;
					  ea = 0;
					  ma = 0;
					  
					}
				    }
				}
			    }
			}
		    }
		}
	    }
	}
    }
  
  assert (ea + ma <= 1);
  assert (eb + mb <= 1);
  assert (i + sa + ea + ma + sb + eb + mb >= 1);
}
