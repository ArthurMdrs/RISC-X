# Export some path variables
export RTL_HOME := $(abspath $(shell pwd)/../rtl)
export RVFI_HOME := $(abspath $(shell pwd)/../fv)
export RVVI_HOME := $(abspath $(shell pwd)/rvvi)
export TB_HOME := $(abspath $(shell pwd))
export RISC_X_PATH := $(abspath $(shell pwd))
export RISCX_UVM_SRC := $(abspath $(shell pwd)/uvm)

PROGS_PATH := $(abspath $(shell pwd)/../programs)


# Set variables used with Google's RISCV-DV
DV_OUT_DIR := $(TB_HOME)/mytest
# DV_FILE_LIST := $(RISCV_DV_ROOT)/files.f
# DV_GEN_TEST := riscv_instr_base_test
# DV_NUM_TESTS := 1
DV_RISCX_TARGET := $(TB_HOME)/riscx_target
DV_ISS_YAML := $(TB_HOME)/iss.yaml
DV_ALL_SIM_TESTS := $(shell tr '\n' ',' < full_test_list.txt | sed 's/,$$//')
DV_SIM_TEST := $(DV_ALL_SIM_TESTS)
DV_RUN_COMMON_FLAGS := --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) \
					   --simulator xlm --noclean --csr_yaml $(TB_HOME)/csr_description.yaml \
					   --custom_target $(DV_RISCX_TARGET) --isa rv32ic_zicsr_zifencei --mabi ilp32 
DV_RUN_CMD := python3 run_mod.py
DV_COV_CMD := python3 cov_mod.py

MTVEC_ALIGNMENT_OPT := +tvec_alignment=8
ifeq ($(strip $(MTVEC_ALIGNMENT_OPT)),)
	GENERATOR_SIM_OPTS :=
else
	GENERATOR_SIM_OPTS := --sim_opts $(MTVEC_ALIGNMENT_OPT)
endif


# Set variables for the simulation
PROG := 
VERBOSE := 0
SEED := 1
SVA := +define+SVA_ON
INPUT := -input restore.tcl
# FILES := -f file_list.f
FILE_LIST := riscx_tb.flist
SIM_TOP := -top tb_top
UVM_HOME := CDNS-1.2
UVM_VERBOSITY := UVM_NONE
UVM_TEST := riscx_dv_test
PLUS_ARG := +progs_path=$(PROGS_PATH)
ifneq ($(strip $(PROG)),)
	PLUS_ARG += +prog=$(PROG)
endif
ifeq ($(strip $(VERBOSE)), 1)
	PLUS_ARG += +verbose=1
endif
XRUN_COMMON_FLAGS := -64bit -timescale 1ns/1ps -access +rwc -sv -uvm -coverage all \
					 -uvmhome $(UVM_HOME) +UVM_NO_RELNOTES +UVM_VERBOSITY=$(UVM_VERBOSITY) +UVM_TESTNAME=$(UVM_TEST) 
XRUN_COMP_FLAGS := $(XRUN_COMMON_FLAGS) \
				   -elaborate -l $(DV_OUT_DIR)/compile.log -xmlibdirpath $(DV_OUT_DIR)
XRUN_SIM_FLAGS := $(XRUN_COMMON_FLAGS) \
				  +define+SIM -svseed $(SEED) $(SIM_TOP) $(SVA) $(PLUS_ARG)

ELF := $(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.o
BIN := $(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.bin
SECTION_FILE = $(patsubst %.o,%.section,$(ELF))


# Dependencies: some files are fetched from external repositories
DEPS := $(RVVI_HOME)/rvviTrace.sv $(RVFI_HOME)/rvfi_macros.vh


##########################################################################################################################


run: sim

sim:
	xrun $(XRUN_SIM_FLAGS) -f $(FILE_LIST) $(XRUN_OPTS)

gui:
	xrun $(XRUN_SIM_FLAGS) -f $(FILE_LIST) -gui -input restore.tcl


##########################################################################################################################


clean-sim:
	rm -rf xcelium.* xrun* .simvision .symbol* waves* jgproject *.log *.diag trace* \
		*.vcd *.evcd *.dump $(DV_OUT_DIR)/*_sim/ $(DV_OUT_DIR)/*.log

clean-asm:
	rm -rf $(DV_OUT_DIR)/asm_test/

clean-cov:
	rm -rf imc.* cov_work/ mdv.log $(DV_COV_DIR) $(COV_REPORT_DIR)

clean-generator:
	rm -rf $(DV_OUT_DIR)

clean: clean-sim clean-asm clean-cov clean-generator