#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

/* Example from Figure 2 */
int main () {

  int x, y, z, w;
  x=y=z=w=0;

  while (__nondet_bool()) {

    if (__nondet_bool()) {x++; y = y+2;}
    else if (__nondet_bool()) {
      if (x >= 4) {x++; y = y+3; z = z+10; w = w+10;}
    }
    else if (x >= z && w > y) {x = -x; y = -y; }
    
  }
  assert (3*x >= y);
}
