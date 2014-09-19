#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main ()
{
  int outfilelen = __undef_int();
  int nchar;
  int out; // index into outfile
  nchar = out = 0;

  if(outfilelen <= 0) return 0;

  while(__undef_bool())
  {
    if(__undef_bool())
    {
      if(__undef_bool())
	break; 

      if(__undef_bool())
      {
	out = 0;
	nchar = 0;
	continue;
      }
      else
      {
	if(__undef_bool())  break;

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

      if(__undef_bool()) break;
    }
  }

  assert(0<=out);//5
  assert(out<outfilelen);
  return 0;
}
