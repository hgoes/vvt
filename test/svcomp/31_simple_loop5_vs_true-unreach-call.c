#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int a = 1;
int b = 2;
int c = 3;
int temp;

pthread_mutex_t lock;

void* thr2(void* arg) {
  for(;;){
    pthread_mutex_lock(&lock);
    pthread_yield();
    temp = a;
    pthread_yield();
    a = b;
    pthread_yield();
    b = c;
    pthread_yield();
    c = temp;
    pthread_yield();
    pthread_mutex_unlock(&lock);
    pthread_yield();
  }
  return 0;
}

void* thr1(void* arg)
{
  while(1) {
    pthread_mutex_lock(&lock);
    pthread_yield();
    assert(a != b);
    pthread_yield();
    pthread_mutex_unlock(&lock);
    pthread_yield();
  }

  return 0;
}

int main() {
  pthread_t t1,t2,t3;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_create(&t3, 0, thr2, 0);
  pthread_yield();
  return 0;
}

