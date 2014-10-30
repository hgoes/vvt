CLANG=clang-3.4
TRGEN=/home/eq/repos/ic3smt_mathsat/TRGen2.jar

BENCHMARKS=$(addsuffix .bc,$(shell cat benchmarks))
BENCHMARKS_CTIGAR=$(addsuffix .c.pre.tr,$(shell cat benchmarks))

ALL: $(BENCHMARKS)
TRGEN: $(BENCHMARKS_CTIGAR)

$(BENCHMARKS): %.bc: %.c
	$(CLANG) -O0 -Wall -c -emit-llvm -DHCTIGAR $< -o $@

$(BENCHMARKS_CTIGAR): %.c.pre.tr: %.c
	cpp -DCTIGAR $< | grep -v '^#' | sed 's/_Bool/bool/' - > $<.pre
	java -jar -ea $(TRGEN) $<.pre
#	rm $<.pre

clean:
	rm -f $(BENCHMARKS)
