#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int count = 0;

void __VERIFIER_atomic_inc()
{
  count++;
}

void __VERIFIER_atomic_dec()
{
  count--;
}

pthread_mutex_t mutexa,mutexb;

void my_thread1() {
  pthread_mutex_lock(&mutexa);
  pthread_yield();
  __VERIFIER_atomic_inc();
  pthread_yield();
  __VERIFIER_atomic_dec();
  pthread_yield();
  pthread_mutex_unlock(&mutexa);
}

void my_thread2() {
  pthread_mutex_lock(&mutexb);
  pthread_yield();
  __VERIFIER_atomic_dec();
  pthread_yield();
  __VERIFIER_atomic_inc();
  pthread_yield();
  pthread_mutex_unlock(&mutexb);
}

void* thr1(void* arg) {
  while(1) {
    pthread_mutex_lock(&mutexa);
    pthread_yield();
    assert(count >= -1);
    pthread_mutex_unlock(&mutexa);
    pthread_yield();
    pthread_mutex_lock(&mutexb);
    pthread_yield();
    assert(count <= 1);
    pthread_mutex_unlock(&mutexb);
    pthread_yield();
  }
  return 0;
}

void* thr2(void* arg) {
  if(__nondet_int())
    my_thread1();
  else
    my_thread2();
  return 0;
}

int main(void)
{
  pthread_t t1,t2,t3;

  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_create(&t3, 0, thr2, 0);
  pthread_yield();
  return 0;
}

