#include <stdbool.h>

void assert(bool);
void assume(bool);
int __undef_int() __attribute__((pure));
bool __undef_bool() __attribute__((pure));

int main(){
  int i;
  int pvlen = __undef_int();
  int tmp___1 ;
  int k;
  int n;
  int j;

  i = k = 0;

  //  pkt = pktq->tqh_first;
  while (__undef_bool())
    i = i + 1;
  if (i > pvlen) {
    pvlen = i;
  }
  i = 0;

  while (__undef_bool()) {
    tmp___1 = i;
    i = i + 1;
    k = k +1;
  }
  while (__undef_bool());

  j = 0;
  n = i;
  //  rand_shuffle(r, (void *)pvbase, (unsigned int )i, sizeof(pkt));
  while (1) {

    assert(k >= 0);
    k = k -1;
    i = i - 1;
    j = j + 1;
    if (j >= n) {
      break;
    }
  }
}
