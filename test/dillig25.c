#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int x;
  int y;
  int i;
  int j;
  x = y = i = j = 0;

  while(__nondet_bool())
  {
    while(__nondet_bool())
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
