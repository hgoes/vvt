//Ticket lock with proportional backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 2).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#ticket

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

unsigned next_ticket = 0;
unsigned now_serving = 0;

void acquire_lock(){
  unsigned my_ticket; 

  my_ticket = __atomic_fetch_add(&next_ticket,1,__ATOMIC_RELAXED); //returns old value; arithmetic overflow is harmless (Alex: it is not if we have 2^64 threads)
  while(1){
    //pause(my_ticket - now_serving);
    // consume this many units of time
    // on most machines, subtraction works correctly despite overflow
    if(now_serving == my_ticket){
      break;
    }
  }
}

void release_lock(){
  now_serving++;
}

int c = 0;
void* thr1(void* arg){
  acquire_lock();
  c++;
  assert(c == 1);
  c--;
  release_lock();
  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

