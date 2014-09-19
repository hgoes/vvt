#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int k = __undef_int();
  int z;
  int x;
  int y;
  int c;
  z = k;
  x = y = 0;

  while(__undef_bool())
  {
    c = 0;
    while(__undef_bool())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
    while(__undef_bool())
    {
      x--;
      y--;
    }
    z=k+y;
  }
  assert(x == y);
}
