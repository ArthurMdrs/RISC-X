# SV_SEED := 1465005197
SV_SEED := random

COV_DIR := $(wildcard cov_work/scope/test_sv*)

TEST := all
ifeq ($(TEST), all)
	UVM_TESTNAME := div_unsigned_test
else ifeq ($(TEST), signed)
	UVM_TESTNAME := div_signed_test
else ifeq ($(TEST), unsigned)
	UVM_TESTNAME := div_unsigned_test
else
	UVM_TESTNAME := undefined_test
endif

sim:
	xrun -access +r -uvm +uvm_set_config_int="*",recording_detail,1 -coverage all -covoverwrite \
		-top top +UVM_VERBOSITY=UVM_MEDIUM -svseed $(SV_SEED) +UVM_TESTNAME=$(UVM_TESTNAME) \
		-DSYSTEM_CLOCK_UNITS_PER_SECOND=100 ../bvm/system_clock.c +incdir+../bvm +UVM_NO_RELNOTES \
		../bvm/*.sv *.sv \
		../../../../rtl/Type_M_Instructions/DIV_HANDSHAKE/opdiv.sv \
		../../../../rtl/Type_M_Instructions/DIV_HANDSHAKE/counter_bit.sv 

wave:
	simvision -NOCOPYRIGHT -input simvision.svcf

cover:
	imc -load $(COV_DIR)

clean:
	rm -rf cov_work waves.shm xcelium.d xrun.* *.log .simvision .bpad *.err

help:
	@echo "Xcelium and VManager need to be installed and environment needs to be set up to use this Makefile."
	@echo "possible arguments to make:"
	@echo "sim - run simulation"
	@echo "wave - show waveforms and transaction diagrams after simulation"
	@echo "       use & to keep the waveform viewer open and reload database after next simulation"
	@echo "clean - remove simulation output files"

