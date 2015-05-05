//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//A counter using locks

#include <pthread.h>
#include <assert.h>

volatile unsigned value;
pthread_mutex_t m;

void * thr1(void* arg) {
  unsigned v = 0;
  pthread_mutex_lock(&m);
#ifndef LIP
  pthread_yield();
#endif
  if(value == 0u-1) {
    pthread_mutex_unlock(&m);
    pthread_yield();
    return 0;
  } else {
    v = value;
#ifndef LIP
    pthread_yield();
#endif
    value = v + 1;
#ifndef LIP
    pthread_yield();
#endif
    pthread_mutex_unlock(&m);
    pthread_yield();
    assert(value > v);
    return 0;
  }
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

