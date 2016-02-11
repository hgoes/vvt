#include <pthread.h>
#include <assert.h>
#include <vvt.h>

void* thr1(void* arg){
  unsigned int x=__nondet_uint(), y=__nondet_uint(), z=__nondet_uint();
  /*__unsigned_uint(x);
  __unsigned_uint(y);
  __unsigned_uint(z);*/
  int i, j=1, k=1;
  for(i=0; i<x; i++) {
    for(j=i+1; j<y; j++) {
      for(k = j; k < z; k++) {
	assert(k > i);
      }
    }
  }
  assert(i == x && (/* uncomment to make error go away: x == 0 ||*/ j == y || y <= x+1) && (x == 0 || y <= x+1 || k == z || z < y)) ;

  return 0;
}

int main()
{
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  //pthread_create(&t2, 0, thr1, 0);
  return 0;
}

