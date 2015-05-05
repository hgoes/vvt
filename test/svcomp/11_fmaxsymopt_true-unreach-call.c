#include <pthread.h>
#include <assert.h>
#include <vvt.h>

#define WORKPERTHREAD 2
#define THREADSMAX 3

int max = 0x80000000;
pthread_mutex_t m;

int storage[WORKPERTHREAD*THREADSMAX];

void findMax(int offset) {
  int i;
  int e;
  int my_max = 0x80000000;

  for(i = offset; i < offset+WORKPERTHREAD; i++) {
#ifndef NOBUG
    e = storage[i];
    pthread_yield();
#else
    e = __nondet_int();
#endif
    if(e > my_max) {
      my_max = e;
    }
    assert(e <= my_max);
  }

  pthread_mutex_lock(&m);
  pthread_yield();
  {
    if(my_max > max) {
      pthread_yield();
      max = my_max;
    }
    pthread_yield();
  }
  pthread_mutex_unlock(&m);
  pthread_yield();
  assert(my_max <= max);
}

void* thr1(void* arg) {
  int offset;

  assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
  //assume(offset < WORKPERTHREAD && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
  
  findMax(offset);

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

