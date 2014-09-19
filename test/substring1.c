#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main () {
  int i, j;
  int from = __undef_int();
  int to;
  int k = __undef_int();
  
  if (!(k >= 0)) return 0;
  if (!(k <= 100)) return 0;
  
  if (!(from >= 0)) return 0;
  if (!(from <= k)) return 0;
  
  i = from;
  j = 0;
  
  while (i < k) {
    i++;
    j++;
  }

  assert (j < 101);
}

