#pragma once

#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

  extern int __nondet_int();
  extern unsigned int __nondet_uint();
  extern long __nondet_long();
  extern size_t __nondet_size();
  extern bool __nondet_bool();
  extern char __nondet_char();

  extern void __unsigned_uint(unsigned int arg);

  extern void __yield(int loc);
  extern void __yield_local(int loc);
  extern bool __act(void *(*thread) (void *),int loc,...);
  extern void __atomic_begin(void);
  extern void __atomic_end(void);
  
  extern void __assume(bool cond);
  extern void __error(void) __attribute__ ((noreturn));
  
  void assume(bool cond) {
    __assume(cond);
#if __has_builtin(__builtin_assume)
    __builtin_assume(cond);
#else
    if(!cond) {
      __builtin_unreachable();
    }
#endif
  }

  // Threads
  typedef struct {
    void* id;
  } __thread_id;

  extern void __thread_spawn(__thread_id* ref,void *(thread) (void*),void* arg);
  extern void __thread_join(__thread_id* ref,void** ret);
  extern void __thread_kill(__thread_id* ref);
  
#ifdef __cplusplus
}
#endif
