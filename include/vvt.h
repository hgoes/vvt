#pragma once

#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

extern int __nondet_int();
extern unsigned int __nondet_uint();
extern size_t __nondet_size();
extern bool __nondet_bool();

extern void __yield(int loc);
extern void __yield_internal(int loc);
extern bool __act(void *(*thread) (void *),int loc,...);
extern void __atomic_begin();
extern void __atomic_end();

extern void assume(bool cond);

#ifdef __cplusplus
}
#endif
