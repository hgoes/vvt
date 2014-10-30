#include "benchmarks.h"

int main ()
{
  NONDET_INT(outfilelen);
  int nchar;
  int out; // index into outfile
  nchar = out = 0;

  if(outfilelen <= 0) return 0;

  while(__nondet_bool())
  {
    if(__nondet_bool())
    {
      if(__nondet_bool())
	break; 

      if(__nondet_bool())
      {
	out = 0;
	nchar = 0;
	continue;
      }
      else
      {
	if(__nondet_bool())  break;

	nchar++;
	if (nchar >= outfilelen)
	  break;

	assert(0<=out);//1
	assert(out<outfilelen);//2
	out++;
      }
    }
    else
    {
      nchar++;
      if (nchar >= outfilelen)
	break;

      assert(0<=out);//3
      assert(out<outfilelen);//4
      out++;

      if(__nondet_bool()) break;
    }
  }

  assert(0<=out);//5
  assert(out<outfilelen);
  return 0;
}
