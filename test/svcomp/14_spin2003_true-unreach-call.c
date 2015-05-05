#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int x=1;
pthread_mutex_t m;

void* thr1(void* arg) {
  pthread_mutex_lock(&m);
  pthread_yield();
  x = 0;
  pthread_yield();
  x = 1;
  pthread_yield();
  assert(x>=1);
  pthread_mutex_unlock(&m);
  return 0;
}

int main() {
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

