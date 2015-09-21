#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int count = 0;

//TODO: Make these actually atomic

void __VERIFIER_atomic_inc()
{
  __atomic_begin();
  count++;
  __atomic_end();
}

void __VERIFIER_atomic_dec()
{
  __atomic_begin();
  count--;
  __atomic_end();
}

pthread_mutex_t mutexa,mutexb;

void my_thread1() {
  pthread_mutex_lock(&mutexa);
  __VERIFIER_atomic_inc();
  __VERIFIER_atomic_dec();
  pthread_mutex_unlock(&mutexa);
}

void my_thread2() {
  pthread_mutex_lock(&mutexb);
  __VERIFIER_atomic_dec();
  __VERIFIER_atomic_inc();
  pthread_mutex_unlock(&mutexb);
}

void* thr1(void* arg) {
  while(1) {
    pthread_mutex_lock(&mutexa);
    assert(count >= -1);
    pthread_mutex_unlock(&mutexa);
    pthread_mutex_lock(&mutexb);
    assert(count <= 1);
    pthread_mutex_unlock(&mutexb);
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
  return 0;
}

