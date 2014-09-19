#include <stdbool.h>

void assert(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main() {
  int i = __undef_int();
  int j = __undef_int();
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
