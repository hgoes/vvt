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

  for(i = offset; i < offset+WORKPERTHREAD; i++) {
    e = storage[i];
    pthread_yield();

    pthread_mutex_lock(&m);
    pthread_yield();
    {
      if(e > max) {
	pthread_yield();
	max = e;
      }
      pthread_yield();
    }
    pthread_mutex_unlock(&m);
    pthread_yield();
    assert(e <= max);
  }
}

void* thr1(void* arg) {
  int offset = __nondet_int();
  
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

