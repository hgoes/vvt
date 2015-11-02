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
    temp = a;
    a = b;
    b = c;
    c = temp;
    pthread_mutex_unlock(&lock);
  }
  return 0;
}

void* thr1(void* arg)
{
  while(1) {
    pthread_mutex_lock(&lock);
    assert(a != b);
    pthread_mutex_unlock(&lock);
  }

  return 0;
}

int main() {
  pthread_t t1,t2,t3;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_create(&t3, 0, thr2, 0);
  return 0;
}

