#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main ()
{
  int fbuflen = __undef_bool();
  int fb;
  if(fbuflen <= 0) return 0;
  fb = 0;
  while (__undef_bool())
  {
    if (__undef_bool())
      break;

    if (__undef_bool())
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
