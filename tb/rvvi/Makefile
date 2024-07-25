# SVA = +define+SVA_ON=1

export RTL_HOME := $(shell pwd)/../../rtl
export RVFI_HOME := $(shell pwd)/../../fv
export TB_HOME := $(shell pwd)
FILES := -f file_list.f
TOP := -top rvvi_tb
PROG := 
ifeq ($(strip $(PROG)),)
  PLUS_ARG :=
else
  PLUS_ARG := +prog=$(PROG)
endif

# SEED = -svseed 2
INPUT = -input restore.tcl

run: rvfi_macros.vh rvviTrace.sv sim

test:
	echo $(AUX)

sim:
	xrun -64bit -sv +define+SIM $(SVA) $(TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc $(SEED)

gui:
	xrun -64bit -sv +define+SIM $(SVA) $(TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc $(SEED) -gui $(INPUT)

jasper:
	jg jg.tcl

rvfi_macros.vh:
	@curl -L -o ./rvfi_macros.vh https://raw.githubusercontent.com/ArthurMdrs/riscv-formal/cv32e40p_v1.8.2/checks/original_checks/rvfi_macros.vh

rvviTrace.sv:
	@curl -L -o ./rvviTrace.sv https://raw.githubusercontent.com/riscv-verification/RVVI/main/source/host/rvvi/rvviTrace.sv

clean:
	rm -rf xcelium.d xrun* .simvision .symbol* waves* jgproject *.log