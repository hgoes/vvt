#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int mThread=0;
int start_main=0;
pthread_mutex_t mStartLock;
int __COUNT__ =0;

void __VERIFIER_atomic_acquire() {
  pthread_mutex_lock(&mStartLock);
}

void __VERIFIER_atomic_release() {
  pthread_mutex_unlock(&mStartLock);
}

void __VERIFIER_atomic_thr1(int PR_CreateThread__RES)
{
      if( __COUNT__ == 0 ) { // atomic check(0);
	mThread = PR_CreateThread__RES; 
	__COUNT__ = __COUNT__ + 1; 
      } else { assert(0); } 
}

void* thr1(void* arg) { //nsThread::Init (mozilla/xpcom/threads/nsThread.cpp 1.31)

  int PR_CreateThread__RES = 1;
  __VERIFIER_atomic_acquire();
  pthread_yield();
  start_main=1;
  pthread_yield();
  __VERIFIER_atomic_thr1(PR_CreateThread__RES);
  pthread_yield();
  __VERIFIER_atomic_release();

  return 0;
}

void __VERIFIER_atomic_thr2(int self)
{
      if( __COUNT__ == 1 ) { // atomic check(1);
	//int rv = self; // self->RegisterThreadSelf();
	__COUNT__ = __COUNT__ + 1;
      } else { assert(0); } 
}

void* thr2(void* arg) { //nsThread::Main (mozilla/xpcom/threads/nsThread.cpp 1.31)

  int self = mThread;
  while (start_main==0) { pthread_yield(); }
  pthread_yield();
  __VERIFIER_atomic_acquire();
  pthread_yield();
  __VERIFIER_atomic_release();
  pthread_yield();
  __VERIFIER_atomic_thr2(self);

  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  pthread_yield();
  thr2(0);

  return 0;
}

