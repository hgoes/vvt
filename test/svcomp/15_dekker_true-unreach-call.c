#include <pthread.h>
#include <assert.h>
#include <vvt.h>
#include <stdbool.h>

bool flag1 = false, flag2 = false; // N boolean flags 
int turn = 0; // integer variable to hold the ID of the thread whose turn is it
int x; // variable to test mutual exclusion

void* thr1(void* arg) {
  flag1 = true;
  while (flag2) {
    if (turn != 0) {
      flag1 = false;
      while (turn != 0) {
      }
      flag1 = 1;
    }
  }
  // begin: critical section
  x = 0;
  assert(x<=0);
  // end: critical section
  turn = 1;
  flag1 = false;

  return 0;
}

void* thr2(void* arg) {
  flag2 = true;
  while (flag1) {
    if (turn != 1) {
      flag2 = false;
      while (turn != 1) {
      }
      flag2 = true;
    }
  }
  // begin: critical section
  x = 1;
  assert(x>=1);
  // end: critical section
  turn = 1;
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

