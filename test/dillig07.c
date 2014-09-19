#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int n = __undef_int();
  int i, j;
  i = j = 0;
  if(!(n >= 0)) return 0;
  while(i<n) {
    i++;
    j++;
  }	
  assert(j < n+1);
}

