//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A counter using locks

#include <pthread.h>
#include <vvt.h>
#include <assert.h>

#define atomic_assert(e) {pthread_mutex_lock(&m);assert(e);pthread_mutex_unlock(&m);}

unsigned value = 0;
pthread_mutex_t m;

/*helpers for the property*/
unsigned inc_flag = 0;
unsigned dec_flag = 0;

unsigned inc() {
  unsigned inc_v = 0;

  pthread_mutex_lock(&m);
  if(value == 0u-1) {
    pthread_mutex_unlock(&m);
    return 0;
  } else {
    inc_v = value;
    inc_flag = 1, value = inc_v + 1; /*set flag, then update*/
    pthread_mutex_unlock(&m);
    atomic_assert(dec_flag || value > inc_v);
    return inc_v + 1;
  }
}

unsigned dec() {
  unsigned dec_v;

  pthread_mutex_lock(&m);
  if(value == 0) {
    pthread_mutex_unlock(&m);
    return 0u-1; /*decrement failed, return max*/
  }else{
    dec_v = value;
    dec_flag = 1, value = dec_v - 1; /*set flag, then update*/
    pthread_mutex_unlock(&m);
    atomic_assert(inc_flag || value < dec_v);
    return dec_v - 1;
  }
}

void* thr1(void* arg){
  int r = __nondet_int();
  if(r){ inc(); }
  else{ dec(); }
  return 0;
}

int main() {
  pthread_t t1,t2;
  pthread_create(&t1,0,thr1,0);
  pthread_create(&t2,0,thr1,0);
  return 0;
}

