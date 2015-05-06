#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int x;
int y;
int b1, b2; // N boolean flags
int X; //variable to test mutual exclusion

void* thr1(void* arg) {
  while (1) {
    b1 = 1;
    pthread_yield();
    x = 1;
    pthread_yield();
    if (y != 0) {
      pthread_yield();
      b1 = 0;
      while (y != 0) { pthread_yield(); };
      pthread_yield();
      continue;
    }
    pthread_yield();
    y = 1;
    pthread_yield();
    if (x != 1) {
      pthread_yield();
      b1 = 0;
      pthread_yield();
      while (b2 >= 1) { pthread_yield(); };
      if (y != 1) {
	pthread_yield();
	while (y != 0) { pthread_yield(); };
	pthread_yield();
	continue;
      }
    }
    break;
  }
  pthread_yield();
  // begin: critical section
  X = 0;
  pthread_yield();
  assert(X <= 0);
  // end: critical section
  pthread_yield();
  y = 0;
  pthread_yield();
  b1 = 0;

  return 0;
}

void* thr2(void* arg) {
  while (1) {
    b2 = 1;
    pthread_yield();
    x = 2;
    pthread_yield();
    if (y != 0) {
      pthread_yield();
      b2 = 0;
      pthread_yield();
      while (y != 0) { pthread_yield(); };
      continue;
    }
    pthread_yield();
    y = 2;
    pthread_yield();
    if (x != 2) {
      pthread_yield();
      b2 = 0;
      pthread_yield();
      while (b1 >= 1) { pthread_yield(); };
      pthread_yield();
      if (y != 2) {
	pthread_yield();
	while (y != 0) { pthread_yield(); };
	pthread_yield();
	continue;
      }
    }
    break;
  }
  pthread_yield();
  // begin: critical section
  X = 1;
  pthread_yield();
  assert(X >= 1);
  pthread_yield();
  // end: critical section
  y = 0;
  pthread_yield();
  b2 = 0;

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

