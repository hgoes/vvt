#pragma once

#include <stddef.h>
#include <stdbool.h>
#include <vvt.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef __thread_id pthread_t;

typedef void pthread_attr_t;

typedef struct {
  int id;
} pthread_mutex_t;

typedef struct {
  void* data;
} pthread_mutexattr_t;

typedef struct {
  int id;
} pthread_rwlock_t;

typedef struct {
  void* data;
} pthread_rwlockattr_t;

typedef struct {
  int id;
} pthread_cond_t;

typedef struct {
  void* data;
} pthread_condattr_t;

// Pthread functions

int pthread_create(pthread_t* pthread,const pthread_attr_t* attr,
                   void *(*start_routine) (void*),void* arg) {
  __thread_spawn(pthread,start_routine,arg);
  return 0;
}

int pthread_yield(void);

int pthread_join(pthread_t* pthread,void** retval) {
  __thread_join(pthread,retval);
  return 0;
}

int pthread_kill(pthread_t* pthread,int sig) {
  __thread_kill(pthread);
  return 0;
}
  
void pthread_exit(void* retval);
  
// Mutex functions

int pthread_mutex_init(pthread_mutex_t *__restrict__ mutex,
                      const pthread_mutexattr_t *__restrict__ attr);

int pthread_mutex_lock(pthread_mutex_t *mutex);

int pthread_mutex_unlock(pthread_mutex_t *mutex);

int pthread_mutex_destroy(pthread_mutex_t *mutex);

// Helper function

bool pthread_mutex_locked(pthread_mutex_t *mutex);
  
// Read-Write lock functions

int pthread_rwlock_init(pthread_rwlock_t *__restrict__ rwlock,
			const pthread_rwlockattr_t *__restrict__ attr);

int pthread_rwlock_destroy(pthread_rwlock_t *rwlock);

int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock);

int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock);

int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock);

int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock);

int pthread_rwlock_unlock(pthread_rwlock_t *rwlock);

#define PTHREAD_MUTEX_INITIALIZER { 0 }

#define pthread_join(thread,retval) pthread_join(&thread,retval)

// Condition variable

void __cond_register(pthread_cond_t* cond,pthread_mutex_t* mutex);
void __cond_wait(pthread_cond_t* cond,pthread_mutex_t* mutex);
void __cond_signal(pthread_cond_t* cond);
void __cond_broadcast(pthread_cond_t* cond);
  
int pthread_cond_init(pthread_cond_t* cond,pthread_condattr_t* cond_attr) {
  return 0;
}

int pthread_cond_signal(pthread_cond_t *cond) {
  __cond_signal(cond);
  return 0;
}

int pthread_cond_broadcast(pthread_cond_t *cond) {
  __cond_broadcast(cond);
  return 0;
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex) {
  __cond_register(cond,mutex);
  __cond_wait(cond,mutex);
  return 0;
}

int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex, const struct timespec *abstime);

int pthread_cond_destroy(pthread_cond_t *cond) {
  return 0;
}

#define PTHREAD_COND_INITIALIZER { 0 }
  
#ifdef __cplusplus
}
#endif
