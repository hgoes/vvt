#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  int id;
} pthread_t;

typedef struct {
  void* data;
} pthread_attr_t;

typedef struct {
  int id;
} pthread_mutex_t;

typedef struct {
  void* data;
} pthread_mutexattr_t;

// Pthread functions

int pthread_create(pthread_t* pthread,const pthread_attr_t* attr,
                   void *(*start_routine) (void*),void* arg);

int pthread_yield(void);

int pthread_join(pthread_t* pthread,void** retval);

void pthread_exit(void* retval);
  
// Mutex functions

int pthread_mutex_init(pthread_mutex_t *__restrict__ mutex,
                      const pthread_mutexattr_t *__restrict__ attr);

int pthread_mutex_lock(pthread_mutex_t *mutex);

int pthread_mutex_unlock(pthread_mutex_t *mutex);

int pthread_mutex_destroy(pthread_mutex_t *mutex);
  
#define pthread_join(thread,retval) pthread_join(&thread,retval)

#ifdef __cplusplus
}
#endif
