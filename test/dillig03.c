#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

int main()
{
  int k;
  int w;
  int z;
  k = w = 1;
  while(__nondet_bool()) {
    z = __nondet_int();
    if(z>5) w++;
    k=k+w;
  }
  assert(k > 0);
}
