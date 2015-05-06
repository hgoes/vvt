#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int count = 0;

pthread_mutex_t mutexa,mutexb;

void my_thread1() {
  pthread_mutex_lock(&mutexa);
  pthread_yield();
  int tmp_count = count;
  pthread_yield();
  count = tmp_count+1;
  pthread_yield();
  tmp_count = count;
  pthread_yield();
  count = tmp_count - 1;
  pthread_yield();
  pthread_mutex_unlock(&mutexa);
  pthread_yield();
  pthread_mutex_lock(&mutexa);
  pthread_yield();
  tmp_count = count;
  pthread_yield();
  count = tmp_count - 1;
  pthread_yield();
  tmp_count = count;
  pthread_yield();
  count = tmp_count + 1;
  pthread_yield();
  pthread_mutex_unlock(&mutexa);
  return;
}

void* thr1(void* arg)
{
  while(1)
  {
    pthread_mutex_lock(&mutexa);
    pthread_yield();
    assert(count >= -1);
    pthread_mutex_unlock(&mutexa);
    pthread_yield();
  }
  return 0;
}

void* thr2(void* arg)
{
  if(__nondet_int())
    my_thread1();
  //else
    //my_thread2();
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

