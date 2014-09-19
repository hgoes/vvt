CLANG=clang-3.4

BENCHMARKS=apache-escape-absolute.bc apache-get-tag.bc barbr.bc barbrprime.bc\
           bind_expands_vars2.bc bkley.bc bk-nat.bc bound.bc cars.bc\
           dillig01.bc dillig03.bc dillig05.bc dillig07.bc dillig12.bc\
           dillig15.bc dillig17.bc dillig19.bc dillig20.bc dillig25.bc\
           dillig28.bc dillig32.bc dillig33.bc dillig37.bc down.bc efm.bc\
           ex1.bc ex2.bc fig1a.bc fig2.bc fragtest_simple.bc gulv.bc\
           gulv_simp.bc gulwani_cegar1.bc gulwani_cegar2.bc gulwani_fig1a.bc\
           hsort.bc hsortprime.bc id_build.bc ken-imp.bc large_const.bc\
           lifnat.bc lifnatprime.bc lifo.bc MADWiFi-encode_ie_ok.bc\
           mergesort.bc nested.bc nested1.bc nested2.bc nested3.bc\
           nested4.bc nested5.bc nested6.bc nested7.bc nested8.bc nested9.bc\
           nest-if.bc nest-if1.bc nest-if2.bc nest-if3.bc nest-if4.bc\
           nest-if5.bc nest-if6.bc nest-if7.bc nest-if8.bc nest-len.bc\
           NetBSD_g_Ctoc.bc NetBSD_glob3_iny.bc NetBSD_loop.bc\
           NetBSD_loop_int.bc pldi08.bc pldi082_unbounded.bc rajamani_1.bc\
           seesaw.bc sendmail-close-angle.bc\
           sendmail-mime7to8_arr_three_chars_no_test_ok.bc\
           sendmail-mime-fromqp.bc seq2.bc seq3.bc seq4.bc seq.bc seq-len.bc\
           seq-proc.bc seq-sim.bc seq-z3.bc simple.bc simple_if.bc\
           simple_nest.bc split.bc string_concat-noarr.bc substring1.bc svd1.bc\
           svd2.bc svd3.bc svd4.bc svd.bc svd-some-loop.bc swim1.bc swim.bc\
           up2.bc up3.bc up4.bc up5.bc up.bc up-nd.bc up-nested.bc\
           xy0.bc xy10.bc xy4.bc xyz2.bc xyz.bc

ALL: $(BENCHMARKS)

$(BENCHMARKS): %.bc: %.c
	$(CLANG) -O0 -Wall -c -emit-llvm $< -o $@

clean:
	rm -f $(BENCHMARKS)
