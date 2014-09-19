#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int flag = __undef_bool();
  int x;
  int y;
  int j;
  int i;
  
  x = y = j = i = 0;
  
  while(__undef_bool())
    {
      x++;
      y++;
      i=i+x;
      j=j+y;
      if(flag)  j=j+1;
    } 
  assert(j > i - 1);
}
