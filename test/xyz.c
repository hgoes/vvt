#include <stdbool.h>

void assert(bool);
int __nondet_int();
bool __nondet_bool();

int main(){
  int x, y, z;
  x = 0; y = 0; z = 0;

  while (__nondet_bool())
  {
    
    x++;
    y++;
    z=z-2;
  }
    while (x > 0){
      z++;z++;
      x--;y--;
    }

    assert (z > -1);
}
