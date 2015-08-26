#include <pthread.h>
#include <assert.h>
#include <vvt.h>

volatile unsigned int count = 0; //shared
pthread_mutex_t MTX = PTHREAD_MUTEX_INITIALIZER; //shared mutex
__thread bool COND = false; //condition variables become local flag indicating whether the thread was signaled

#define cnd_wait(c,m){ \
  pthread_mutex_unlock(&MTX); \
  assume(c); \
  c = false; \
  pthread_mutex_lock(&MTX); }

#define cnd_broadcast(c) (c = true) //BP must be post-processed manually by changing "b*_COND := 1" to "b*_COND$ := 1"

void Barrier2() {  
  pthread_mutex_lock(&MTX);
  count++;
  if (count == 3) {
    cnd_broadcast(COND); //pthread_cond_broadcast(&cond);
    count = 0; }
  else
    cnd_wait(COND,MTX); //pthread_cond_wait(&cond, &m);
  pthread_mutex_unlock(&MTX); }
  
void* thr1(void* arg){
  Barrier2();
  assert(0);

  return 0;
} //should not fail for <3 threads

int main(){
  pthread_t t1,t2,t3;
  pthread_create(&t1,0,thr1,0);
  pthread_create(&t2,0,thr1,0);
  //pthread_create(&t3,0,thr1,0);
  return 0;
}
