#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main ()
{
  int x;
  int y;
  int z = __undef_int();

  x = y = 0;

  while (__undef_bool()){
    x = x + 10;
    y = y + 1;
  }

  assert (x > z || y < z + 1);
}
