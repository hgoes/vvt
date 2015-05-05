//Symmetry-Aware Predicate Abstraction for Shared-Variable Concurrent Programs (Extended Technical Report). CoRR abs/1102.2330 (2011)

#include <pthread.h>
#include <stdint.h>
#include <vvt.h>
#include <assert.h>

unsigned int r = 0;
unsigned int s = 0;

void __VERIFIER_atomic_inc_r()
{
  unsigned int value = __atomic_fetch_add(&r,1,__ATOMIC_RELAXED);
  assume(value!=-1); //to avoid overflows
}

void* thr1(void* arg){
  unsigned int l = 0;

  __VERIFIER_atomic_inc_r();
  pthread_yield();
  if(r == 1){
    unsigned int tmp_s;
  L3:
    tmp_s = s;
    pthread_yield();
    s = tmp_s + 1;
    pthread_yield();
    l = l + 1;
    assert(s == l);
    pthread_yield();
    goto L3;
  }

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  pthread_yield();
  return 0;
}

