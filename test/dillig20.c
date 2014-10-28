#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int x = __nondet_int();
  int y = __nondet_int();
  int k = __nondet_int();
  int j;
  int i = __nondet_int();
  int n = __nondet_int();
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
    if(__nondet_bool())
      m = j;
    j++;
  }
  if(j < n)
    return 0;
  assert(x + y == k);
  assert(n < 1 || m > -1);
  assert(n < 1 || m < n);
}

