#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int x,m;
  int n = __nondet_int();

  x = 0;
  m = 0;
  while( x < n ) {
    if(__nondet_bool())
      m = x;
    x++;
  }
  if( n > 0 )
    {
      assert( 0<=m);
      assert(m<n);
    }
}
