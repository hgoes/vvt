#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main(){

  int x, y, z;
  x = y = z = 0;

  while (__nondet_bool()) {
    x++;
    y++;
    z=z-2;
  }
    while (x >= 1){
      z++;z++;
      x--;y--;
    }

    if(x <= 0)
      if (z >= 1)
        assert(0);
}
