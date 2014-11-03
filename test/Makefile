CLANG=clang-3.4
TRGEN=/home/eq/repos/ic3smt_mathsat/TRGen2.jar

BENCHMARKS=$(addsuffix .bc,$(shell cat benchmarks))
BENCHMARKS_CTIGAR=$(addsuffix .c.pre.tr,$(shell cat benchmarks))
BENCHMARKS_CPACHECKER=$(addsuffix .cpachecker.c,$(shell cat benchmarks))

ALL: $(BENCHMARKS)
TRGEN: $(BENCHMARKS_CTIGAR)
CPACHECKER: $(BENCHMARKS_CPACHECKER)

$(BENCHMARKS): %.bc: %.c
	$(CLANG) -O0 -Wall -c -emit-llvm -DHCTIGAR $< -o $@

$(BENCHMARKS_CTIGAR): %.c.pre.tr: %.c
	cpp -DCTIGAR $< | grep -v '^#' | sed 's/_Bool/bool/' - > $<.pre
	java -jar -ea $(TRGEN) $<.pre
	rm $<.pre

$(BENCHMARKS_CPACHECKER): %.cpachecker.c: %.c
	cpp -DCPACHECKER $< | sed 's/_Bool/int/' > $@

clean:
	rm -f $(BENCHMARKS)
	rm -f $(BENCHMARKS_CTIGAR)
	rm -f $(BENCHMARKS_CPACHECKER)
