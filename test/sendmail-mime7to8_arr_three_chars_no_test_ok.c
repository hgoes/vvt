#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main ()
{
  int fbuflen = __nondet_bool();
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
