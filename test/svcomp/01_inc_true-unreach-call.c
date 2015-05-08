//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//A counter using locks

#include <pthread.h>
#include <assert.h>

unsigned value;
pthread_mutex_t m;

void * thr1(void* arg) {
  unsigned v = 0;
  pthread_mutex_lock(&m);
  if(value == 0u-1) {
    pthread_mutex_unlock(&m);
    return 0;
  } else {
    v = value;
    value = v + 1;
    pthread_mutex_unlock(&m);
    assert(value > v);
    return 0;
  }
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

