#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main ()
{
  int x;
  int y;
  int z = __nondet_int();

  x = y = 0;

  while (__nondet_bool()){
    x = x + 10;
    y = y + 1;
  }

  assert (x > z || y < z + 1);
}
