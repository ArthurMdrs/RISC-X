# SVA = +define+SVA_ON=1

export RTL_HOME := $(shell pwd)/../../rtl
export RVFI_HOME := $(shell pwd)/../../fv
export TB_HOME := $(shell pwd)
FILES := -f file_list.f
TOP := -top riscv_dv_tb

PROGS_PATH := $(shell pwd)/../basic_tb/programs
PROG := 
PLUS_ARG := +progs_path=$(PROGS_PATH)
ifeq ($(strip $(PROG)),)
	PLUS_ARG +=
else
	PLUS_ARG += +prog=$(PROG)
endif

# SEED = -svseed 2
INPUT = -input restore.tcl

ELF=/home/pedro.medeiros/Tools/riscv-dv/mytest/asm_test/riscv_arithmetic_basic_test_0.o

run: rvfi_macros.vh rvviTrace.sv sim

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
	
rars:
	python3 run_rars.py $(PROGS_PATH) $(PROG)

elf2hex:
	@python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt

sim-elf:
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	xrun -64bit -sv +define+SIM $(SVA) $(TOP) $(FILES) \
		 -timescale 1ns/1ps -access +rwc $(SEED) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +check_regs=0 +check_mem=0 +print_trace=1

sim-elf-gui:
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	xrun -64bit -sv +define+SIM $(SVA) $(TOP) $(FILES) -gui $(INPUT) \
		 -timescale 1ns/1ps -access +rwc $(SEED) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +check_regs=0 +check_mem=0 +print_trace=1
