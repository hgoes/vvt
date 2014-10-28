#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int n = __nondet_int();
  int i, j;
  i = j = 0;
  if(!(n >= 0)) return 0;
  while(i<n) {
    i++;
    j++;
  }	
  assert(j < n+1);
}

