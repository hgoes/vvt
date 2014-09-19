#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int x,m;
  int n = __undef_int();

  x = 0;
  m = 0;
  while( x < n ) {
    if(__undef_bool())
      m = x;
    x++;
  }
  if( n > 0 )
    {
      assert( 0<=m);
      assert(m<n);
    }
}
