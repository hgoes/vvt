#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int x;
  int y;
  int i;
  int j;
  x = y = i = j = 0;

  while(__undef_bool())
  {
    while(__undef_bool())
    {
       if(x==y)
          i++;
       else
          j++;
    }
    if(i>=j)
    {
       x++;
       y++;
    }
    else
       y++;
  }
  assert(i > j-1);
}
