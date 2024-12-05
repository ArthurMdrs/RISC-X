COV_DIR := $(wildcard cov_work/scope/test_sv*)

sim:
	xrun -access +r -uvm +uvm_set_config_int="*",recording_detail,1 -coverage all -covoverwrite \
		-top top +UVM_VERBOSITY=UVM_HIGH -svseed random \
		-DSYSTEM_CLOCK_UNITS_PER_SECOND=100 ../bvm/system_clock.c +incdir+../bvm \
		../bvm/*.sv *.sv \
		../../../../rtl/Type_M_Instructions/MULT_HANDSHAKE/rtl/multiplier.sv \
		
wave:
	simvision -NOCOPYRIGHT -input simvision.svcf

cover:
	imc -load $(COV_DIR)

clean:
	rm -rf cov_work waves.shm xcelium.d xrun.* *.log .simvision

help:
	@echo "Xcelium and VManager need to be installed and environment needs to be set up to use this Makefile."
	@echo "possible arguments to make:"
	@echo "sim - run simulation"
	@echo "wave - show waveforms and transaction diagrams after simulation"
	@echo "       use & to keep the waveform viewer open and reload database after next simulation"
	@echo "clean - remove simulation output files"

