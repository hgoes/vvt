#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main (){

  int x;
  int y = __nondet_int();
  x = -50;
  while (x < 0){
     x = x + y;
     y++;
  }

  assert (y >= 0);
}
