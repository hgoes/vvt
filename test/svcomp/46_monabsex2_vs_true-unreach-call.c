#include <pthread.h>
#include <assert.h>
#include <vvt.h>

bool s = false;
__thread bool l = false;

void* thr1(void* arg)
{
  assert(!l || s);
  s = s || 1;
  l = true; //overapproximates

  return 0;
}

int main() {
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

