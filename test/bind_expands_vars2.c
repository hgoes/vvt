#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int();
bool __undef_bool();


int main() {
  int cpoff = __undef_int();
  int n1 = __undef_int();
  int n2 = __undef_int();
  int mc_i;
  int maxdata = __undef_int();
  assume (maxdata > 0 ); 
  assume (n1 <= maxdata * 2); 
  assume (cpoff <= n1); 
  assume (n2 <= maxdata*2 - n1); 
  mc_i = 0;
  while (mc_i < n2) {
    assert (cpoff+mc_i < maxdata * 2);
    mc_i++;
  }
  return 0;
}
