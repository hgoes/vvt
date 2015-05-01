#pragma once

#include <stddef.h>
#include <stdbool.h>

extern int __nondet_int();
extern unsigned int __nondet_uint();
extern size_t __nondet_size();
extern bool __nondet_bool();

extern void __yield(int loc);
extern bool __act(void *(*thread) (void *),int loc,...);

extern void assume(bool cond);
