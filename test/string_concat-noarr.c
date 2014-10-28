#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i, j;
  i = 0;
  while(__nondet_bool()){
    i++;
  }
  if(i >= 100) return 0;
  j = 0;
  while(__nondet_bool()){
    i++;
    j++;
  }
  if(j >= 100) return 0;
  assert( i < 200 );
  return 0;
}
