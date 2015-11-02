#include <pthread.h>
#include <vvt.h>
#include <assert.h>

#define N 3
#define M 2

int accounts[N];
pthread_mutex_t locks[N];

void transaction(int from,int to,int sum) {
  pthread_mutex_lock(&locks[from]);
  pthread_yield();
  pthread_mutex_lock(&locks[to]);
#ifndef OPTLOCKS
  pthread_yield();
#endif
  accounts[from] -= sum;
#ifndef OPTLOCKS
  pthread_yield();
#endif
  accounts[to] += sum;
#ifndef OPTLOCKS
  pthread_yield();
#endif
  pthread_mutex_unlock(&locks[to]);
#ifndef OPTLOCKS
  pthread_yield();
#endif
  pthread_mutex_unlock(&locks[from]);
  pthread_yield();
}

void* thread1(void* arg) {
  while(__nondet_bool()) {
    int from = __nondet_int();
    assume(from >= 0);
    assume(from < N);
    int to = __nondet_int();
    assume(to >= 0);
    assume(to < N);
    assume(from != to);
    int amount = __nondet_int();
    transaction(from,to,amount);
  }
  return NULL;
}

int main(int argc,char** argv) {
  int sum = __nondet_int();
  assume(sum>=0);
  int i;
  int remaining=sum;
  for(i=0;i<N;i++) {
    int ded = __nondet_int();
    assume(ded>=0);
    assume(ded<=remaining);
    accounts[i] = ded;
    remaining-=ded;
  }
  assume(remaining==0);
  pthread_t threads[M];
  for(i=0;i<M;i++) {
    pthread_create(&threads[i],NULL,thread1,NULL);
  }
  pthread_yield();
  for(i=0;i<M;i++) {
    pthread_join(threads[i],NULL);
  }
  int sum2=0;
  for(i=0;i<N;i++) {
    sum2+=accounts[i];
  }
  assert(sum==sum2);
  return 0;
}
