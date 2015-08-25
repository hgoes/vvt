VVT_INCLUDE=/home/eq/ic3/include
LIPTON=/home/eq/repos/lipton/LiptonPass
CLANG=clang-3.4
CLANG_OPTS=-mem2reg -internalize-public-api-list=main -internalize -inline -loops -loop-simplify -loop-rotate -lcssa -loop-unroll

BENCHMARKS=$(shell cat benchmarks)
LLVM_FILES=$(addsuffix .ll,$(BENCHMARKS))
LIPTON_FILES=$(addsuffix .lipton.ll,$(BENCHMARKS))
VVT_FILES=$(addsuffix .l,$(BENCHMARKS))

ALL: $(VVT_FILES)

## Disable implicit rule
%.c : %.l

$(LLVM_FILES): %.ll: %.c
	$(CLANG) -O0 -I${VVT_INCLUDE} -emit-llvm -c $< $(CLANG_ARGS) -o - |\
	opt $(CLANG_OPTS) - -o -\
	| llvm-dis -o $@ -

$(LIPTON_FILES): %.lipton.ll: %.ll
	llvm-as $< -o - | $(LIPTON) | opt -mem2reg -instnamer - -o - | llvm-dis -o $@ -

$(VVT_FILES): %.l: %.lipton.ll
	vvt-enc < $< | vvt-opt | vvt-predicates | vvt-pp > $@

clean:
	rm -f $(LLVM_FILES) $(LIPTON_FILES) $(VVT_FILES)
