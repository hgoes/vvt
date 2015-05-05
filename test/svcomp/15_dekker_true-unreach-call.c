#include <pthread.h>
#include <assert.h>
#include <vvt.h>
#include <stdbool.h>

bool flag1 = false, flag2 = false; // N boolean flags 
int turn = 0; // integer variable to hold the ID of the thread whose turn is it
int x; // variable to test mutual exclusion

void* thr1(void* arg) {
  flag1 = true;
  pthread_yield();
  while (flag2) {
    pthread_yield();
    if (turn != 0) {
      pthread_yield();
      flag1 = false;
      pthread_yield();
      while (turn != 0) { pthread_yield(); };
      pthread_yield();
      flag1 = 1;
    }
  }
  pthread_yield();
  // begin: critical section
  x = 0;
  pthread_yield();
  assert(x<=0);
  // end: critical section
  pthread_yield();
  turn = 1;
  pthread_yield();
  flag1 = false;

  return 0;
}

void* thr2(void* arg) {
  flag2 = true;
  pthread_yield();
  while (flag1) {
    pthread_yield();
    if (turn != 1) {
      pthread_yield();
      flag2 = false;
      while (turn != 1) { pthread_yield(); };
      pthread_yield();
      flag2 = true;
    }
  }
  pthread_yield();
  // begin: critical section
  x = 1;
  pthread_yield();
  assert(x>=1);
  pthread_yield();
  // end: critical section
  turn = 1;
  pthread_yield();
  flag2 = false;

  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  thr2(0);

  return 0;
}

