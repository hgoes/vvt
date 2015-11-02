#include <pthread.h>
#include <assert.h>
#include <vvt.h>
#include <stdbool.h>

#define MONITOR_EQ(x,y) \
{ \
  while(1) \
  {\
    pthread_mutex_lock(&mutex);\
    assert(x==y);\
    pthread_mutex_unlock(&mutex);\
  }\
}

int g0 = 0,g1 = 0,x = 0;
bool lock = 0;
pthread_mutex_t mutex;

void* thr3(void* arg)
{
  pthread_mutex_lock(&mutex);
  if(__nondet_bool()) {
    g0=0;
    g1=0;
    lock=false;
  }
  pthread_mutex_unlock(&mutex);
  
  pthread_mutex_lock(&mutex);
  if(lock) {
    x=1;
    assert(g0==1 && g1==1);
  }
  pthread_mutex_unlock(&mutex);

  return 0;
}

void* thr2(void* arg)
{
  MONITOR_EQ(g0,g1);

  return 0;
}

void* thr1(void* arg) {
  pthread_mutex_lock(&mutex);
  g0=1;
  g1=1;
  pthread_mutex_unlock(&mutex);
  lock=1;
  return 0;
}

int main() {
  pthread_t t1,t2,t3,t4;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_create(&t3, 0, thr3, 0);
  pthread_create(&t4, 0, thr3, 0);
  return 0;
}

