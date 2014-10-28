#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int flag = __nondet_bool();
  int x;
  int y;
  int j;
  int i;
  
  x = y = j = i = 0;
  
  while(__nondet_bool())
    {
      x++;
      y++;
      i=i+x;
      j=j+y;
      if(flag)  j=j+1;
    } 
  assert(j > i - 1);
}
