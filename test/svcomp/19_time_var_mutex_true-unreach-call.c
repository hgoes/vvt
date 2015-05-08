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
  if(inode == 0){
    pthread_mutex_lock(&m_busy);
    busy = 1;
    pthread_mutex_unlock(&m_busy);
    inode = 1;
  }
  block = 1;
  assert(block == 1);
  pthread_mutex_unlock(&m_inode);
  return 0;
}

void * thr2(void* arg) {
  pthread_mutex_lock(&m_busy);
  if(busy == 0){
    block = 0;
    assert(block == 0);
  }
  pthread_mutex_unlock(&m_busy);
  return 0;
}

int main()
{
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  thr2(0);

  return 0;
}

