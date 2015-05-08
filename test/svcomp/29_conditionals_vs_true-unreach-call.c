#include <pthread.h>
#include <assert.h>
#include <vvt.h>

pthread_mutex_t m;

void* thr1(void* arg) {
  int x;
  int y;
  
  x = __nondet_int();
  y = __nondet_int();
  
  int z;
  pthread_mutex_lock(&m);
  if(x == y) {
    z = 0;
  } else {
    z = 1;
  }
  
  if(z == 0) {
    assert(x == y);
  } else {
    assert(x != y);
  }
  pthread_mutex_unlock(&m);
  return 0;
}

int main() {
  pthread_t t1,t2;
  
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

