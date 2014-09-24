CLANG=clang-3.4

BENCHMARKS=$(addsuffix .bc,$(shell cat benchmarks))

ALL: $(BENCHMARKS)

$(BENCHMARKS): %.bc: %.c
	$(CLANG) -O0 -Wall -c -emit-llvm $< -o $@

clean:
	rm -f $(BENCHMARKS)
