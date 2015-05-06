#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int x, y;
pthread_rwlock_t lock;

void* thr1(void* arg) { //writer
  pthread_rwlock_wrlock(&lock);
  pthread_yield();
  x = 3;
  pthread_yield();
  pthread_rwlock_unlock(&lock);
  return 0;
}


void* thr2(void* arg) { //reader
  pthread_rwlock_rdlock(&lock);
  pthread_yield();
  y = x;
  pthread_yield();
  assert(y == x);
  pthread_yield();
  pthread_rwlock_unlock(&lock);
  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  pthread_yield();
  thr2(0);
  
  return 0;
}

