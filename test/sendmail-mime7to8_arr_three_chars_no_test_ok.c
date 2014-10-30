#include "benchmarks.h"

int main ()
{
  NONDET_INT(fbuflen);
  int fb;
  if(fbuflen <= 0) return 0;
  fb = 0;
  while (__nondet_bool())
  {
    if (__nondet_bool())
      break;

    if (__nondet_bool())
      break;

    assert(0<=fb);
    assert(fb<fbuflen);
    fb++;
    if (fb >= fbuflen-1)
      fb = 0;

    assert(0<=fb);
    assert(fb<fbuflen);

    fb++;
    if (fb >= fbuflen-1)
      fb = 0;

    assert(0<=fb);
    assert(fb<fbuflen);

    fb++;
    if (fb >= fbuflen-1)
      fb = 0;
  }

  if (fb > 0)
  {
    assert(0<=fb);
    assert(fb<fbuflen);
  }

  return 0;
}
