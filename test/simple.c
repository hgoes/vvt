#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int x;
  int n = __undef_int();
  x = 0;
  
  if(n <= 0 ) return 0;
  while( x < n ){
    x++;
  }
  assert( x<=n );
}
