#include <stdbool.h>

void assert(bool);
void assume(bool);
int __nondet_int() __attribute__((pure));
bool __nondet_bool() __attribute__((pure));

int main () {
  int i, j;
  int from = __nondet_int();
  int to;
  int k = __nondet_int();
  
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

