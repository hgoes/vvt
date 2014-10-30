#include "benchmarks.h"

int main (){

  int x;
  int y;
  
  x = y = 0;
  
  while (__nondet_bool()){
    x = x + 4;
    y = y + 1;
  }

  while (x > 0){
    x = x - 4;
    y = y - 1;
  }

  assert (y > -1);
}
