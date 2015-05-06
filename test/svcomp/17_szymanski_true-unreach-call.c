#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int flag1 = 0, flag2 = 0; // N integer flags 
int x; // variable to test mutual exclusion

void* thr1(void* arg) {
  while (1) {
    flag1 = 1;
    pthread_yield();
    while (flag2 >= 3);
    pthread_yield();
    flag1 = 3;
    pthread_yield();
    if (flag2 == 1) {
      pthread_yield();
      flag1 = 2;
      pthread_yield();
      while (flag2 != 4);
    }
    pthread_yield();
    flag1 = 4;
    pthread_yield();
    while (flag2 >= 2);
    pthread_yield();
    // begin critical section
    x = 0;
    pthread_yield();
    assert(x<=0);
    pthread_yield();
    // end critical section
    while (2 <= flag2 && flag2 <= 3);
    pthread_yield();
    flag1 = 0;
  }

  return 0;
}

void* thr2(void* arg) {
  while (1) {
    flag2 = 1;
    pthread_yield();
    while (flag1 >= 3);
    pthread_yield();
    flag2 = 3;
    pthread_yield();
    if (flag1 == 1) {
      pthread_yield();
      flag2 = 2;
      pthread_yield();
      while (flag1 != 4);
    }
    pthread_yield();
    flag2 = 4;
    pthread_yield();
    while (flag1 >= 2);
    pthread_yield();
    // begin critical section
    x = 1;
    pthread_yield();
    assert(x>=1);
    pthread_yield();
    // end critical section
    while (2 <= flag1 && flag1 <= 3);
    pthread_yield();
    flag2 = 0;
  }

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

