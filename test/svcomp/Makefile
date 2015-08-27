VVT_INCLUDE=/home/eq/ic3/include
LIPTON=/home/eq/repos/lipton/LiptonPass
CLANG=clang-3.4
CLANG_OPTS=-mem2reg -internalize-public-api-list=main -internalize -inline -loops -loop-simplify -loop-rotate -lcssa -loop-unroll
TIMEOUT=500s

BENCHMARKS=$(shell grep -v ^\# benchmarks )
LLVM_FILES=$(addsuffix .ll,$(BENCHMARKS))
LIPTON_FILES=$(addsuffix .lipton.ll,$(BENCHMARKS))
VVT_FILES=$(addsuffix .l,$(BENCHMARKS))
OUTPUT_FILES=$(addsuffix .output,$(BENCHMARKS))

ALL: $(VVT_FILES)

## Disable implicit rule
%.c : %.l

llvm_files: $(LLVM_FILES)

$(LLVM_FILES): %.ll: %.c
	$(CLANG) -O0 -I${VVT_INCLUDE} -emit-llvm -c $< $(CLANG_ARGS) -o - |\
	opt $(CLANG_OPTS) - -o -\
	| llvm-dis -o $@ -

lipton_files: $(LIPTON_FILES)

$(LIPTON_FILES): %.lipton.ll: %.ll
	llvm-as $< -o - | $(LIPTON) | opt -mem2reg -constprop -simplifycfg -globaldce -instnamer - -o - | llvm-dis -o $@ -

vvt_files: $(VVT_FILES)

$(VVT_FILES): %.l: %.lipton.ll
	vvt-enc < $< | vvt-opt | vvt-predicates | vvt-pp > $@

output_files: $(OUTPUT_FILES)

$(OUTPUT_FILES): %.output: %.l
	vvt-verify --stats --timeout=500s < $< > $@

clean:
	rm -f $(LLVM_FILES) $(LIPTON_FILES) $(VVT_FILES) $(OUTPUT_FILES)
