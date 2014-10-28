#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int n = __nondet_int();
  int k;
  int i;
  int j;
  k = i = 1;
  j = 0;
  while(i<=n-1) {
    assert(k > i-1);
    j=0;
    while(j<=i-1) {
      k = k + (i-j);
      j++;
    }
    if(j < i)
      return 0;
    i++;
  } 
}

