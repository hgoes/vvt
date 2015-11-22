#pragma once

#include <vvt.h>
#include <assert.h>
#include <string.h>
#include <pthread.h>
#include <stdio.h>

#define __VERIFIER_assume __assume
#define __VERIFIER_error __error
#define __VERIFIER_assert assert
#define __VERIFIER_nondet_bool __nondet_bool
#define __VERIFIER_nondet_int __nondet_int
unsigned int __VERIFIER_nondet_uint() {
  unsigned int res = __nondet_uint();
  __unsigned_uint(res);
  return res;
}
#define __VERIFIER_nondet_long __nondet_long
#define __VERIFIER_nondet_char __nondet_char
#define __VERIFIER_nondet_pointer() 0

#define CAS1(v,e,u,r) *r = __sync_bool_compare_and_swap(v,e,u)
#define CAS2(v,e,u,r,f) { __atomic_begin(); *r = __sync_bool_compare_and_swap(v,e,u); *f=*f||*r; __atomic_end(); }

#define GET_MACRO(_1,_2,_3,_4,_5,NAME,...) NAME
#define __VERIFIER_atomic_CAS(...) GET_MACRO(__VA_ARGS__,CAS2,CAS1)(__VA_ARGS__)
#define __VERIFIER_atomic_TAS(lock,cond) { *cond = __atomic_test_and_set(lock,__ATOMIC_RELAXED); }
