#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

/* Example from Figure 1 (a) */
int main () {

  int x,y;

  x=0;
  y=0;
  
  while (__undef_bool()) {
    x++;
    y++;
  }
  
  while (x > 0 || x < 0) {
    x--;
    y--;
  }
  
  assert (y >= 0 && y <= 0);

} 
