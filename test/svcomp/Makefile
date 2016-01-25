VVT_INCLUDE=/home/eq/ic3/include
LIPTON=/home/eq/repos/lipton/LiptonPass
CLANG=clang-3.5
AS=llvm-as-3.5
DIS=llvm-dis-3.5
OPT=opt-3.5
CLANG_OPTS=-mem2reg -internalize-public-api-list=main -internalize -inline -loops -loop-simplify -loop-rotate -lcssa -loop-unroll
LIPTON_OPT=-mem2reg -constprop -instsimplify -correlated-propagation -die -simplifycfg -globaldce -instnamer
VVT_OPT=value-set=5 inline simplify slice
TIMEOUT=15m

BENCHMARKS=$(shell grep -v ^\# benchmarks )
LLVM_FILES=$(addsuffix .ll,$(BENCHMARKS))
LIPTON_FILES=$(addsuffix .lipton.ll,$(BENCHMARKS))
LIPTON_Y_FILES=$(addsuffix .lipton-y.ll,$(BENCHMARKS))
LIPTON_N_FILES=$(addsuffix .lipton-n.ll,$(BENCHMARKS))
LIPTON_S_FILES=$(addsuffix .lipton-s.ll,$(BENCHMARKS))
VVT_FILES=$(addsuffix .l,$(BENCHMARKS))
VVT_Y_FILES=$(addsuffix .y.l,$(BENCHMARKS))
VVT_N_FILES=$(addsuffix .n.l,$(BENCHMARKS))
VVT_S_FILES=$(addsuffix .s.l,$(BENCHMARKS))
OUTPUT_FILES=$(addsuffix .output,$(BENCHMARKS))
OUTPUT_Y_FILES=$(addsuffix .y.output,$(BENCHMARKS))
OUTPUT_N_FILES=$(addsuffix .n.output,$(BENCHMARKS))
OUTPUT_S_FILES=$(addsuffix .s.output,$(BENCHMARKS))

ALL: vvt_files

## Disable implicit rule
%.c : %.l

llvm_files: $(LLVM_FILES)

$(LLVM_FILES): %.ll: %.c
	$(CLANG) -O0 -I${VVT_INCLUDE} -emit-llvm -c $< $(CLANG_ARGS) -o - |\
	$(OPT) $(CLANG_OPTS) - -o -\
	| $(DIS) -o $@ -

lipton_files: $(LIPTON_FILES) $(LIPTON_Y_FILES) $(LIPTON_N_FILES) $(LIPTON_S_FILES)

$(LIPTON_FILES): %.lipton.ll: %.ll
	$(AS) $< -o - | $(LIPTON) | $(OPT) $(LIPTON_OPT) - -o - | $(DIS) -o $@ -

$(LIPTON_Y_FILES): %.lipton-y.ll: %.ll
	$(AS) $< -o - | $(LIPTON) -y | $(OPT) $(LIPTON_OPT) - -o - | $(DIS) -o $@ -

$(LIPTON_N_FILES): %.lipton-n.ll: %.ll
	$(AS) $< -o - | $(LIPTON) -n | $(OPT) $(LIPTON_OPT) - -o - | $(DIS) -o $@ -

$(LIPTON_S_FILES): %.lipton-s.ll: %.ll
	$(AS) $< -o - | $(LIPTON) -s | $(OPT) $(LIPTON_OPT) - -o - | $(DIS) -o $@ -

vvt_files: $(VVT_FILES) $(VVT_Y_FILES) $(VVT_N_FILES) $(VVT_S_FILES)

$(VVT_FILES): %.l: %.lipton.ll
	vvt-enc < $< | vvt-opt $(VVT_OPT) | vvt-predicates | vvt-pp > $@

$(VVT_Y_FILES): %.y.l: %.lipton-y.ll
	vvt-enc < $< | vvt-opt $(VVT_OPT) | vvt-predicates | vvt-pp > $@

$(VVT_N_FILES): %.n.l: %.lipton-n.ll
	vvt-enc < $< | vvt-opt $(VVT_OPT) | vvt-predicates | vvt-pp > $@

$(VVT_S_FILES): %.s.l: %.lipton-s.ll
	vvt-enc < $< | vvt-opt $(VVT_OPT) | vvt-predicates | vvt-pp > $@

output_files: $(OUTPUT_FILES) $(OUTPUT_Y_FILES) $(OUTPUT_N_FILES) $(OUTPUT_S_FILES)

$(OUTPUT_FILES): %.output: %.l
	vvt-verify --stats --timeout=$(TIMEOUT) < $< > $@

$(OUTPUT_Y_FILES): %.output: %.l
	vvt-verify --stats --timeout=$(TIMEOUT) < $< > $@

$(OUTPUT_N_FILES): %.output: %.l
	vvt-verify --stats --timeout=$(TIMEOUT) < $< > $@

$(OUTPUT_S_FILES): %.output: %.l
	vvt-verify --stats --timeout=$(TIMEOUT) < $< > $@

time.dat: output_files
	./extract.sh time > time.dat

clean:
	rm -f $(LLVM_FILES)\
              $(LIPTON_FILES) $(LIPTON_Y_FILES) $(LIPTON_N_FILES) $(LIPTON_S_FILES)\
              $(VVT_FILES) $(VVT_Y_FILES) $(VVT_N_FILES) $(VVT_S_FILES)\
              $(OUTPUT_FILES) $(OUTPUT_Y_FILES) $(OUTPUT_N_FILES) $(OUTPUT_S_FILES)
