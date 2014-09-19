#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int x = __undef_int();
  int y = __undef_int();
  int k = __undef_int();
  int j;
  int i = __undef_int();
  int n = __undef_int();
  int m;
  m = 0;
  if((x+y) != k)
    return 0;
  j = 0;
  while(j<=n-1) {
    if(j==i)
      {
	x++;
	y--;
      }else
      {
	y++;
	x--;
      }
    if(__undef_bool())
      m = j;
    j++;
  }
  if(j < n)
    return 0;
  assert(x + y == k);
  assert(n < 1 || m > -1);
  assert(n < 1 || m < n);
}

