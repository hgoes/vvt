//Simple test_and_set lock with exponential backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 1).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#tas

#include <pthread.h>
#include <stdbool.h>
#include <assert.h>
#include <vvt.h>

#define unlocked false
#define locked true
bool lock = unlocked;

void acquire_lock(){
  int delay;
  int cond;
  
  delay = 1;
  cond = __atomic_test_and_set(&lock,__ATOMIC_RELAXED);
  while(cond == locked){
    //pause(delay);
    if(delay*2 > delay) 
      delay *= 2;
    cond = __atomic_test_and_set(&lock,__ATOMIC_RELAXED);
  }
  assert(cond != lock);
}

void release_lock(){
  assert(lock != unlocked);
  lock = unlocked; 
}

int c = 0;
void* thr1(void *arg){
  while(1){
    acquire_lock();
    c++;
    assert(c == 1);
    c--;
    release_lock();
  }
  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

