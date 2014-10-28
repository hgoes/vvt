#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int x;
  int n = __nondet_int();
  x = 0;
  
  if(n <= 0 ) return 0;
  while( x < n ){
    x++;
  }
  assert( x<=n );
}
