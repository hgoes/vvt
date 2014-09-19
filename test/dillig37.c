#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

int main() {
  int x;
  int m;
  int n = __undef_int();
  x = m = 0;
  while(x<=n-1) {
    if(__undef_bool()) {
      m = x;
    }
    x= x+1;
  }
  if(x < n)
    return 0;
  assert(n<1 || m > -1);
  assert(n<1 || m < n);
}
