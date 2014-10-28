#include <stdbool.h>

void assert(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main() {
  int i = __nondet_int();
  int j = __nondet_int();
  int x;
  int y;
  x = i;
  y = j;
  while(x!=0) {
	x--;
	y--;
  }
  if (i==j) assert (y == 0);
}
