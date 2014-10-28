#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

/* Example from Figure 1 (a) */
int main () {

  int x,y;

  x=0;
  y=0;
  
  while (__nondet_bool()) {
    x++;
    y++;
  }
  
  while (x > 0 || x < 0) {
    x--;
    y--;
  }
  
  assert (y >= 0 && y <= 0);

} 
