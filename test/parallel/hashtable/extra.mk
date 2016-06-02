Makefile: MkMake.hs
	runghc MkMake.hs > Makefile

results-insert-empty-bmc: results-bmc
	grep '^t[0-9]*-empty[0-9]*-p1' results-bmc > results-insert-empty-bmc

results-insert-empty-bmc-n: results-bmc-n
	grep '^t[0-9]*-empty[0-9]*-p1' results-bmc-n > results-insert-empty-bmc-n

results-insert-empty-ic3: results-ic3
	grep '^t[0-9]*-empty[0-9]*-p1' results-ic3 > results-insert-empty-ic3

results-insert-empty-ic3-n: results-ic3-n
	grep '^t[0-9]*-empty[0-9]*-p1' results-ic3-n > results-insert-empty-ic3-n

insert-empty.pdf: insert-empty.r results-insert-empty-bmc results-insert-empty-bmc-n results-insert-empty-ic3 results-insert-empty-ic3-n
	Rscript insert-empty.r

results-insert-full-bmc: results-bmc
	grep '^t4-full7-p[0-9]*' results-bmc > results-insert-full-bmc

results-insert-full-bmc-n: results-bmc-n
	grep '^t4-full7-p[0-9]*' results-bmc-n > results-insert-full-bmc-n

results-insert-full-ic3: results-ic3
	grep '^t4-full7-p[0-9]*' results-ic3 > results-insert-full-ic3

results-insert-full-ic3-n: results-ic3-n
	grep '^t4-full7-p[0-9]*' results-ic3-n > results-insert-full-ic3-n

insert-full.pdf: insert-full.r results-insert-full-bmc results-insert-full-bmc-n  results-insert-full-ic3 results-insert-full-ic3-n
	Rscript insert-full.r

results-insert-mixed-bmc: results-bmc
	grep '^t[0-9]*-mixed5-p4' results-bmc > results-insert-mixed-bmc

results-insert-mixed-bmc-n: results-bmc-n
	grep '^t[0-9]*-mixed5-p4' results-bmc-n > results-insert-mixed-bmc-n

results-insert-mixed-ic3: results-ic3
	grep '^t[0-9]*-mixed5-p4' results-ic3 > results-insert-mixed-ic3

results-insert-mixed-ic3-n: results-ic3-n
	grep '^t[0-9]*-mixed5-p4' results-ic3-n > results-insert-mixed-ic3-n

insert-mixed.pdf: insert-mixed.r results-insert-mixed-bmc results-insert-mixed-bmc-n results-insert-mixed-ic3 results-insert-mixed-ic3-n
	Rscript insert-mixed.r
