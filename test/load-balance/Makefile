LIPTON=/home/eq/repos/lipton/LiptonPass
TIMEOUT=15m
OPTS=--ineq
VVT=vvt encode $(OPTS) --lipton="$(LIPTON)"

ALL: result-1.output result-n-1.output result-2.output result-n-2.output result-3.output result-n-3.output

load-balance-1.l: load-balance.c
	$(VVT) -DN=1 load-balance.c -o load-balance-1.l

load-balance-n-1.l: load-balance.c
	$(VVT) -DN=1 load-balance.c -o load-balance-n-1.l

result-1.output: load-balance-1.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-1.l > result-1.output

result-n-1.output: load-balance-n-1.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-n-1.l > result-n-1.output

load-balance-2.l: load-balance.c
	$(VVT) -DN=2 load-balance.c -o load-balance-2.l

load-balance-n-2.l: load-balance.c
	$(VVT) -DN=2 load-balance.c -o load-balance-n-2.l

result-2.output: load-balance-2.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-2.l > result-2.output

result-n-2.output: load-balance-n-2.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-n-2.l > result-n-2.output

load-balance-3.l: load-balance.c
	$(VVT) -DN=3 load-balance.c -o load-balance-3.l

load-balance-n-3.l: load-balance.c
	$(VVT) -DN=3 load-balance.c -o load-balance-n-3.l

result-3.output: load-balance-3.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-3.l > result-3.output

result-n-3.output: load-balance-n-3.l
	vvt-verify --stats --timeout=$(TIMEOUT) < load-balance-n-3.l > result-n-3.output
