#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

int main()
{
  int k;
  int w;
  int z;
  k = w = 1;
  while(__undef_bool()) {
    z = __undef_int();
    if(z>5) w++;
    k=k+w;
  }
  assert(k > 0);
}
