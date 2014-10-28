#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int();
bool __nondet_bool();

/*
 * From CAV'12 by Sharma et al.
 */

int main() {
  int x;
  int y;
  int n;
  x = y = n = 0;
  while(__nondet_bool()) {
      x++;
      y++;
  }
  while(x <= n - 1 || x >= n + 1) {
      x--;
      y--;
  }
  if(x != n)
    return 0;
  assert(y == n);
}
