#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int x = __undef_int();
  int y = __undef_int();

  if (0 > x) return 0;  
  if (x > 2) return 0;
  if (0 > y) return 0;  
  if (y > 2) return 0;
  while(__undef_bool()) {
	x=x+2;
	y=y+2;
  }
  if( y >= 0 ) 
    if( y <= 0 ) 
      if( 4 <= x ) 
	assert( x < 4 );
}
