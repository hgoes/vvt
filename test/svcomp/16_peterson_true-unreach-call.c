#include <pthread.h>
#include <assert.h>
#include <vvt.h>

int turn; // integer variable to hold the ID of the thread whose turn is it
int x; // variable to test mutual exclusion
int flag1 = 0, flag2 = 0; // boolean flags

void* thr1(void* arg) { // frontend produces 12 transitions from this thread. It would be better if it would produce only 8!
  flag1 = 1;
  turn = 1;
  int tmp_flag2,tmp_turn;
  do {
    tmp_flag2 = flag2;
    tmp_turn = turn;
  } while (tmp_flag2==1 && tmp_turn==1);
  // begin: critical section
  x = 0;
  assert(x<=0);
  // end: critical section
  flag1 = 0;

  return 0;
}

void* thr2(void* arg) {
  flag2 = 1;
  turn = 0;
  int tmp_flag1,tmp_turn;
  do {
    tmp_flag1 = flag1;
    tmp_turn = turn;
  } while (tmp_flag1==1 && tmp_turn==0);
  // begin: critical section
  x = 1;
  assert (x>=1);
  // end: critical section
  flag2 = 0;

  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  thr2(0);

  return 0;
}

