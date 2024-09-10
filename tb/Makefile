######################################################################################################################
##########################                            PATH VARS                             ##########################
######################################################################################################################

RISC_X_ROOT := $(abspath $(shell pwd)/..)
export RTL_HOME := $(abspath $(RISC_X_ROOT)/rtl)
export RVFI_HOME := $(abspath $(RISC_X_ROOT)/fv)
export TB_HOME := $(abspath $(shell pwd))
TOOLS_HOME := $(abspath $(RISC_X_ROOT)/tools)

export RISCX_UVM_SRC := $(abspath $(TB_HOME)/uvm)
export RISCV_DV_ROOT := $(abspath $(TOOLS_HOME)/riscv-dv)
RISCV_DV_ADDS := $(abspath $(TOOLS_HOME)/additions/riscv-dv)

# export RVVI_HOME := $(abspath $(shell pwd)/rvvi)

export RISC_X_PATH := $(abspath $(shell pwd))

PROGS_PATH := $(abspath $(TB_HOME)/programs)



######################################################################################################################
##########################                          RISCV-DV VARS                           ##########################
######################################################################################################################

ISA := rv32ic_zicsr_zifencei
ABI := ilp32
DV_OUT_DIR := $(TB_HOME)/mytest
# DV_FILE_LIST := $(RISCV_DV_ROOT)/files.f
# DV_GEN_TEST := riscv_instr_base_test
# DV_NUM_TESTS := 1
DV_RISCX_TARGET := $(RISCV_DV_ADDS)/riscx_target
DV_ISS_YAML := $(RISCV_DV_ADDS)/iss.yaml
DV_STEPS := iss_sim
DV_ALL_SIM_TESTS := $(shell tr '\n' ',' < full_test_list.txt | sed 's/,$$//')
DV_SIM_TEST := $(DV_ALL_SIM_TESTS)
DV_RUN_COMMON_FLAGS := --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) --iss_timeout 600 \
					   --noclean --simulator xlm --custom_target $(DV_RISCX_TARGET) \
					   --iss_yaml $(DV_ISS_YAML) --csr_yaml $(RISCV_DV_ADDS)/csr_description.yaml \
					   --isa $(ISA) --mabi $(ABI) 
DV_RUN_CMD := cd $(RISCV_DV_ROOT) && python3 run.py
DV_COV_CMD := cd $(RISCV_DV_ROOT) && python3 cov.py

MTVEC_ALIGNMENT_OPT := +tvec_alignment=8
ifneq ($(strip $(MTVEC_ALIGNMENT_OPT)),)
	GENERATOR_SIM_OPTS := --sim_opts $(MTVEC_ALIGNMENT_OPT)
endif

ASM_TEST := 1_basic.s



######################################################################################################################
##########################                             SIM VARS                             ##########################
######################################################################################################################

# PROG := 
SEED := 1
SVA := +define+SVA_ON
INPUT := -input restore.tcl
FILE_LIST := riscx_tb.flist
SIM_TOP := -top tb_top
UVM_HOME := CDNS-1.2
UVM_VERBOSITY := UVM_MEDIUM
UVM_TEST := riscx_dv_test
PLUS_ARG := +progs_path=$(PROGS_PATH)
ifneq ($(strip $(PROG)),)
	PLUS_ARG += +prog=$(PROG)
endif
VERBOSE := 0
ifeq ($(strip $(VERBOSE)), 1)
	PLUS_ARG += +verbose=1
endif
START_ADDR := 8000_0000
ifneq ($(strip $(START_ADDR)),)
	PLUS_ARG += +start_addr=$(START_ADDR)
endif
BIN := $(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.bin
ifneq ($(strip $(BIN)),)
	PLUS_ARG += +bin=$(BIN)
endif
RVVI_LOG := $(shell date +%Y-%m-%d_%H-%M-%S).log
ifneq ($(strip $(RVVI_LOG)),)
	PLUS_ARG += +rvvi_log=$(RVVI_LOG)
endif

XRUN_COMMON_FLAGS := -64bit -timescale 1ns/1ps -access +rwc -sv -uvm -coverage all -covoverwrite \
					 -uvmhome $(UVM_HOME) +UVM_NO_RELNOTES +UVM_VERBOSITY=$(UVM_VERBOSITY) +UVM_TESTNAME=$(UVM_TEST) 

XRUN_COMP_FLAGS := $(XRUN_COMMON_FLAGS) \
				   -elaborate -l $(DV_OUT_DIR)/compile.log -xmlibdirpath $(DV_OUT_DIR)

XRUN_SIM_FLAGS := $(XRUN_COMMON_FLAGS) \
				  +define+SIM -svseed $(SEED) $(SIM_TOP) $(SVA) $(PLUS_ARG)

# ELF := $(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.o
# BIN := $(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.bin
# SECTION_FILE = $(patsubst %.o,%.section,$(ELF))



# Dependencies: some files are fetched from external repositories
DEPS := $(RISCV_DV_ROOT) $(RVFI_HOME)/rvfi_macros.vh

run: sim

$(RVFI_HOME)/rvfi_macros.vh: 
	@curl -L -o $(RVFI_HOME)/rvfi_macros.vh https://raw.githubusercontent.com/ArthurMdrs/riscv-formal/cv32e40p_v1.8.2/checks/original_checks/rvfi_macros.vh



######################################################################################################################
##########################                           SIM TARGETS                            ##########################
######################################################################################################################

sim: $(DEPS)
	xrun $(XRUN_SIM_FLAGS) -f $(FILE_LIST) $(XRUN_OPTS)

gui: $(DEPS)
	xrun $(XRUN_SIM_FLAGS) -f $(FILE_LIST) $(XRUN_OPTS) -gui $(INPUT)



######################################################################################################################
##########################                         RISCV-DV TARGETS                         ##########################
######################################################################################################################

# riscv-dv-sim: $(DEPS)
# 	$(MAKE) sim RVVI_LOG=$(subst /asm_test/,/risc-x_sim/,$(BIN:.bin=.log)) UVM_VERBOSITY=UVM_NONE

riscv-dv-sim: $(DEPS)
	$(MAKE) sim UVM_VERBOSITY=UVM_NONE

compile-instr-generator:
	@$(DV_RUN_CMD) --co --output $(DV_OUT_DIR) \
		--custom_target $(DV_RISCX_TARGET) --simulator xlm

gen-and-compile-asm:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so --steps gen,gcc_compile $(GENERATOR_SIM_OPTS)

run-dv-steps:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --steps $(DV_STEPS) --iss=risc-x,spike

sim-iss:
	@$(MAKE) run-dv-steps DV_STEPS=iss_sim

compare:
	@$(MAKE) run-dv-steps DV_STEPS=iss_cmp

sim-and-compare:
	@$(MAKE) run-dv-steps DV_STEPS=iss_sim,iss_cmp

gen-sim-cmp:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so $(GENERATOR_SIM_OPTS) \
		--iss=risc-x,spike

# dv-full: compile-instr-generator gen-and-compile-asm sim-and-compare
dv-full: compile-instr-generator gen-sim-cmp

spike-sim:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --steps iss_sim --iss=spike

# csr-test is WIP
csr-test:
	@python3 $(RISCV_DV_ROOT)/scripts/gen_csr_test.py --xlen 32 --iterations 1 --out $(DV_OUT_DIR)/asm_test --end_signature_addr 0 --csr_file $(TB_HOME)/csr_description.yaml

# c-test does NOT work yet (run_c is not compiling correctly??)
c-test:
	@$(DV_RUN_CMD) --output $(DV_OUT_DIR) --simulator xlm --noclean --iss_timeout 600 \
		--custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi $(ABI) \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike --gcc_opts="-I$(PROGS_PATH)/include" \
		--c_test $(PROGS_PATH) --debug debug.log

# asm-test IS WORKING!
asm-test:
	@$(DV_RUN_CMD) --output $(DV_OUT_DIR) --simulator xlm --noclean --iss_timeout 600 \
		--custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi $(ABI) \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike --gcc_opts="-I$(PROGS_PATH)/include" \
		--asm_test $(PROGS_PATH)/$(ASM_TEST)

asm-test-dir:
	@$(DV_RUN_CMD) --output $(DV_OUT_DIR) --simulator xlm --noclean --iss_timeout 600 \
		--custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi $(ABI) \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike --gcc_opts="-I$(PROGS_PATH)/include" \
		--asm_test $(PROGS_PATH)



######################################################################################################################
##########################                              CLEAN                               ##########################
######################################################################################################################

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



######################################################################################################################
##########################                              IGNORE                              ##########################
######################################################################################################################

TIMESTAMP := $(shell date +%Y-%m-%d_%H-%M-%S).log

echo:
	@echo $(patsubst %/asm_test/%.bin,%/risc-x_sim/%.log,$(BIN))
	@echo $(patsubst %.bin,%.log,$(BIN))
	@echo $(subst /asm_test/,/risc-x_sim/,$(BIN:.bin=.log))
	@echo $(subst .bin,.log,$(BIN))

echo2:
	$(MAKE) echo
