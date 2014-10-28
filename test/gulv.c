#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main(){
  int x, y, w, z;
  x = y = w = z = 0;
  while (__nondet_bool()) {
    if (__nondet_bool())
      {x = x+1; y = y+100;}
    else if (__nondet_bool()){
      if (x >= 4)
	{x = x+1; y = y+1;}
    }
    else if (y > 10*w && z >= 100*x)
      {y = -y;}
    w = w+1; z = z+10;
 
  }
  assert (x < 4 || y > 2);
  return 0;
}
