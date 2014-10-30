#include "benchmarks.h"

int main(){
  int x, y;
  x = 0; y = 0;
  while (__nondet_bool()) {
    if (__nondet_bool())
      {x = x+1; y = y+100;}
    else if (__nondet_bool()){
      if (x >= 4)
	{x = x+1; y = y+1;}
    }
  }
  assert (x < 4 || y > 2);
}
