#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main (){

  int x;
  int y = __undef_int();
  x = -50;
  while (x < 0){
     x = x + y;
     y++;
  }

  assert (y >= 0);
}
