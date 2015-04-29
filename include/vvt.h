#pragma once

#include <stddef.h>
#include <stdbool.h>

extern int __nondet_int();
extern size_t __nondet_size();

extern void __yield(int loc);
extern bool __act(void *(*thread) (void *),int loc,...);
