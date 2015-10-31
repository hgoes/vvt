#!/bin/bash

if [ "$#" -lt 1 ]; then
    echo "Supply an input (c/c++) file"
    exit 1
fi

BINDIR=`dirname $0`
CLANG=clang-3.4
VVT_INCLUDE=${BINDIR}/../include
LIPTON=${BINDIR}/LiptonPass
LIPTON_OPT="-mem2reg -constprop -instsimplify -correlated-propagation -die -simplifycfg -globaldce -instnamer"
LLVM_OPT=opt-3.5
CLANG_OPTS="-mem2reg -loops -loop-simplify -loop-rotate -lcssa -loop-unroll"
VVT_OPT="simplify slice value-set=2 inline simplify"

INCLUDE_FIXES="s/\(^\|[^_]\)inline//;\
               s/volatile//;\
               s/void __VERIFIER_atomic_CAS/void __NOTUSED_atomic_CAS/;\
               s/void __VERIFIER_atomic_TAS/__NOT_USED_atomic_TAS/;\
               s/void main/int main/;\
               s/void __VERIFIER_assert/void __VERIFIER_assert_NOT_USED/;\
               s/int pthread_create/int __NOT_USED_pthread_create/;\
               s/int pthread_join/int __NOT_USED_pthread_join/;\
               s/void pthread_exit/void __NOT_USED_pthread_exit/;\
               s/typedef .* pthread_t;//;\
               s/} pthread_attr_t;/};/;\
               s/typedef .* pthread_attr_t;//;\
               s/} pthread_mutex_t;/};/;\
               s/} pthread_mutexattr_t;/};/;\
               s/} pthread_cond_t;/};/;\
               s/} pthread_condattr_t;/};/;\
               s/int pthread_cond_init/int __NOT_USED_pthread_cond_init/;\
               s/int pthread_cond_timedwait/int __NOT_USED_pthread_cond_timedwait/;\
               s/} pthread_rwlock_t;/};/;\
               s/} pthread_rwlockattr_t;/};/;\
               s/typedef .* size_t;//;\
               s/typedef .* wchar_t;//;\
               s/int (.*malloc)/int __NOT_USED_malloc/;\
               s/int exit(/int __NOT_USED_exit(/;\
               s/int *fprintf *(/int __NOT_USED_fprintf(/;\
               s/int *printf *(/int __NOT_USED_printf(/;\
               s/void __VERIFIER_assume(/void __NOT_USED_assume(/;\
               s/void *\* *\(thr[0-9]*\|qrcu.*\|reader\|writer\|allocator\|de_allocator\)()/void *\1(void* __NOT_USED_ARG)/"

sed "${INCLUDE_FIXES}" < $1 |\
    ${CLANG} -O0 -x c -I${VVT_INCLUDE} -include ${VVT_INCLUDE}/svcomp.h -emit-llvm -c - -o - |\
    ${LLVM_OPT} -mem2reg |\
    ${BINDIR}/vvt-svcomp atomic threads=2 inline locks |\
    ${LLVM_OPT} ${CLANG_OPTS} - -o - |\
    ${LIPTON} |\
    ${LLVM_OPT} ${LIPTON_OPT} |\
    ${BINDIR}/vvt-enc |\
    ${BINDIR}/vvt-opt -s "${BINDIR}/z3 -smt2 -in" ${VVT_OPT} |\
    ${BINDIR}/vvt-predicates |\
    ${BINDIR}/vvt-verify\
	     --backend="cons:${BINDIR}/z3 -smt2 -in"\
	     --backend="lifting:${BINDIR}/z3 -smt2 -in"\
	     --backend="domain:${BINDIR}/z3 -smt2 -in"\
	     --backend="init:${BINDIR}/z3 -smt2 -in"\
	     --backend="interp:${BINDIR}/mathsat"
