#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main() {

  int n = __nondet_int();
  int i;
  int k = __nondet_int();
  int j;
  if(n < 1)
    return 0;
  if(k < n)
    return 0;
  j = 0;
  while( j <= n-1 ) {
    j++;
    k--;
  } 
  if(j < n)
    return 0;
  assert(k > -1);
}
