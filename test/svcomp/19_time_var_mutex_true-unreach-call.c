#include <pthread.h>
#include <assert.h>
#include <vvt.h>


int block;
int busy; // boolean flag indicating whether the block has be an allocated to an inode
int inode;

pthread_mutex_t m_inode; // protects the inode
pthread_mutex_t m_busy;  // protects the busy flag

void * thr1(void* arg) {
  pthread_mutex_lock(&m_inode);
  pthread_yield();
  if(inode == 0){
    pthread_yield();
    pthread_mutex_lock(&m_busy);
    pthread_yield();
    busy = 1;
    pthread_yield();
    pthread_mutex_unlock(&m_busy);
    pthread_yield();
    inode = 1;
  }
  pthread_yield();
  block = 1;
  pthread_yield();
  assert(block == 1);
  pthread_yield();
  pthread_mutex_unlock(&m_inode);
  return 0;
}

void * thr2(void* arg) {
  pthread_mutex_lock(&m_busy);
  pthread_yield();
  if(busy == 0){
    pthread_yield();
    block = 0;
    pthread_yield();
    assert(block == 0);
  }
  pthread_yield();
  pthread_mutex_unlock(&m_busy);
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

