extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <pthread.h>
#include <assert.h>
#include <vvt.h>

/*
to correctly model the cv_broadcast(COND) statement "b1_COND := 1;" must be manually changed to "b1_COND$ := 1;" in the abstract BP
*/

#define cv_wait(c,m){ \
  c = false; \
  pthread_mutex_unlock(&m); \
  assume(c); \
  pthread_mutex_lock(&m); }

#define cv_broadcast(c) c = true //overapproximates semantics (for threader)

#define mtx_lock(m) pthread_mutex_lock(&m);assert(pthread_mutex_locked(&m)); //acquire lock and ensure no other thread unlocked it
#define mtx_unlock(m) pthread_mutex_unlock(&m)

pthread_mutex_t MTX = PTHREAD_MUTEX_INITIALIZER;
__thread bool COND = false;

volatile int refctr = 0;

void put_client(int client){
	mtx_lock(MTX);
	--refctr;
	if (refctr == 0) {
		cv_broadcast(COND); }
	mtx_unlock(MTX);
  assert(1);
}

void rdma_addr_unregister_client(int client){
	put_client(client);
	mtx_lock(MTX);
	if (refctr) {
		cv_wait(COND,MTX); }
	mtx_unlock(MTX);
  assert(1);
}

void queue_req(/*struct addr_req *req*/){
	mtx_lock(MTX);
	mtx_unlock(MTX);
  assert(1);
}

void process_req(/*void *ctx, int pending*/){
	mtx_lock(MTX);
	mtx_unlock(MTX);
  assert(1);
}

void rdma_resolve_ip(/*struct rdma_addr_client *client,struct sockaddr *src_addr, struct sockaddr *dst_addr,struct rdma_dev_addr *addr, int timeout_ms,void (*callback)(int status, struct sockaddr *src_addr,struct rdma_dev_addr *addr, void *context),void *context*/){
	mtx_lock(MTX);
	refctr++;
	mtx_unlock(MTX);
	if(__nondet_int()){
		mtx_lock(MTX);
		refctr--;
		mtx_unlock(MTX); }
  assert(1);
}

void rdma_addr_cancel(/*struct rdma_dev_addr *addr*/){
	mtx_lock(MTX);
	mtx_unlock(MTX);
  assert(1);
}

void* thr1(void* arg){
  while(1)
    switch(__nondet_int()){
    case 0: rdma_addr_unregister_client(__nondet_int()); break;
    case 1: queue_req(); break;
    case 2: process_req(); break;
    case 3: rdma_resolve_ip(); break;
    case 4: rdma_addr_cancel(); break; 
  }

  return 0;
}

int main(){
  pthread_t t1,t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr1, 0);
  return 0;
}

