#pragma once

#include <stddef.h>

extern void *malloc (size_t __size) __attribute__ ((__nothrow__ )) __attribute__ ((__malloc__));
extern void *calloc (size_t __size,size_t __num) __attribute__ ((__nothrow__ )) __attribute__ ((__malloc__));
extern void free(void* __ptr) __attribute__ ((__nothrow__ ));

extern void exit(int code) __attribute__ ((__noreturn__));
