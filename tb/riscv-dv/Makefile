export RISC_X_ROOT := $(abspath $(shell pwd)/../..)
export RTL_HOME := $(abspath $(RISC_X_ROOT)/rtl)
export RVFI_HOME := $(abspath $(RISC_X_ROOT)/fv)
export TB_HOME := $(abspath $(shell pwd))
export RISC_X_PATH := $(abspath $(shell pwd))
export RVVI_HOME := $(abspath $(RISC_X_ROOT)/tb/rvvi)
export RISCV_DV_ROOT := $(abspath $(RISC_X_ROOT)/tools/riscv-dv)

ISA := rv32ic_zicsr_zifencei

DV_OUT_DIR := $(TB_HOME)/mytest
DV_FILE_LIST := $(RISCV_DV_ROOT)/files.f
DV_GEN_TEST := riscv_instr_base_test
DV_NUM_TESTS := 1
DV_RISCX_TARGET := $(TB_HOME)/riscx_target
DV_ISS_YAML := $(TB_HOME)/iss.yaml
DV_ALL_SIM_TESTS := $(shell tr '\n' ',' < full_test_list.txt | sed 's/,$$//')
DV_SIM_TEST := $(DV_ALL_SIM_TESTS)
DV_RUN_COMMON_FLAGS := --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) \
					   --simulator xlm --noclean --csr_yaml $(TB_HOME)/csr_description.yaml \
					   --custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi ilp32 
DV_RUN_CMD := cd $(RISCV_DV_ROOT) && python3 run.py
DV_COV_CMD := cd $(RISCV_DV_ROOT) && python3 cov.py

MTVEC_ALIGNMENT_OPT := +tvec_alignment=8
ifeq ($(strip $(MTVEC_ALIGNMENT_OPT)),)
	GENERATOR_SIM_OPTS :=
else
	GENERATOR_SIM_OPTS := --sim_opts $(MTVEC_ALIGNMENT_OPT)
endif

PROGS_PATH := $(abspath $(shell pwd)/../programs)
PROG := 
VERBOSE := 0
PLUS_ARG := +progs_path=$(PROGS_PATH)
ifneq ($(strip $(PROG)),)
	PLUS_ARG += +prog=$(PROG)
endif
ifeq ($(strip $(VERBOSE)), 1)
	PLUS_ARG += +verbose=1
endif

SEED = 1
# SVA = +define+SVA_ON=1
INPUT = -input restore.tcl

ELF=$(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.o
BIN=$(DV_OUT_DIR)/asm_test/$(DV_SIM_TEST)_0.bin
SECTION_FILE=$(patsubst %.o,%.section,$(ELF))

XRUN_COMMON_FLAGS := -64bit -timescale 1ns/1ps -access +rwc -sv -uvm -uvmhome $(UVMHOME)
XRUN_COMP_FLAGS := $(XRUN_COMMON_FLAGS) -elaborate -l $(DV_OUT_DIR)/compile.log -xmlibdirpath $(DV_OUT_DIR)
XRUN_SIM_FLAGS := $(XRUN_COMMON_FLAGS) +define+SIM -svseed $(SEED)
FILES := -f file_list.f
SIM_TOP := -top riscv_dv_tb

DEPS := $(RVVI_HOME)/rvviTrace.sv $(RVFI_HOME)/rvfi_macros.vh

##########################################################################################################################

run: $(DEPS) sim

sim: $(DEPS)
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

gui: $(DEPS)
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED) -gui $(INPUT)

$(RVFI_HOME)/rvfi_macros.vh: 
	@curl -L -o $(RVFI_HOME)/rvfi_macros.vh https://raw.githubusercontent.com/ArthurMdrs/riscv-formal/cv32e40p_v1.8.2/checks/original_checks/rvfi_macros.vh

RVVI_COMMIT := 20240403.0
$(RVVI_HOME)/rvviTrace.sv:
	@curl -L -o $(RVVI_HOME)/rvviTrace.sv https://raw.githubusercontent.com/riscv-verification/RVVI/$(RVVI_COMMIT)/source/host/rvvi/rvviTrace.sv

rars:
	python3 run_rars.py $(PROGS_PATH) $(PROG)

elf2hex:
	@python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt

sim-elf: $(DEPS)
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	python3 elf2hex.py $(ELF) $(SECTION_FILE) 1
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +bin=$(BIN) +section=$(SECTION_FILE) \
		 +check_regs=0 +check_mem=0 +print_trace=1 +verbose=$(VERBOSE) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

sim-elf-gui: $(DEPS)
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	python3 elf2hex.py $(ELF) $(SECTION_FILE) 1
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) -gui $(INPUT) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +bin=$(BIN) +section=$(SECTION_FILE) \
		 +check_regs=0 +check_mem=0 +print_trace=1 +verbose=$(VERBOSE) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

##########################################################################################################################
# Attempt to do RISCV-DV stuff manually
# compile-instr-generator:
# 	xrun $(XRUN_COMP_FLAGS) +incdir+riscx_target +incdir+$(RISCV_DV_ROOT)/user_extension \
# 		-f $(DV_FILE_LIST) -top riscv_instr_gen_tb_top

# run-instr-generator: $(DV_OUT_DIR)
# 	xrun $(XRUN_SIM_FLAGS) -R -xmlibdirpath $(DV_OUT_DIR) +UVM_TESTNAME=$(DV_GEN_TEST) +num_of_tests=$(DV_NUM_TESTS)

##########################################################################################################################

compile-instr-generator:
	@$(DV_RUN_CMD) --co --output $(DV_OUT_DIR) \
		--custom_target $(DV_RISCX_TARGET) --simulator xlm

gen-and-compile-asm:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so --steps gen,gcc_compile $(GENERATOR_SIM_OPTS)

sim-dv:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --steps iss_sim \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike

compare:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --steps iss_cmp \
		--iss=risc-x,spike

dv-full: compile-instr-generator gen-and-compile-asm sim-dv compare

gen-sim-cmp:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so $(GENERATOR_SIM_OPTS) \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike

sim-and-compare:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so --steps iss_sim,iss_cmp \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike

spike-sim:
	@$(DV_RUN_CMD) $(DV_RUN_COMMON_FLAGS) --so --steps iss_sim \
		--iss_yaml $(DV_ISS_YAML) --iss=spike

csr-test:
	@python3 $(RISCV_DV_ROOT)/scripts/gen_csr_test.py --xlen 32 --iterations 1 --out $(DV_OUT_DIR)/asm_test --end_signature_addr 0 --csr_file $(TB_HOME)/csr_description.yaml

# c-test does NOT work yet (run_c is not compiling correctly??)
c-test:
	@$(DV_RUN_CMD) --output $(DV_OUT_DIR) --simulator xlm --noclean \
		--custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi ilp32 \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike --gcc_opts="-I$(PROGS_PATH)/include" \
		--c_test $(PROGS_PATH) --debug debug.log

# asm-test IS WORKING!
asm-test:
	@$(DV_RUN_CMD) --output $(DV_OUT_DIR) --simulator xlm --noclean \
		--custom_target $(DV_RISCX_TARGET) --isa $(ISA) --mabi ilp32 \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike --gcc_opts="-I$(PROGS_PATH)/include" \
		--asm_test $(PROGS_PATH)

##########################################################################################################################

DV_COV_DIR := $(DV_OUT_DIR)/cov
COV_TESTS_DIR := $(DV_COV_DIR)/default
# export COV_TEST_RUN := $(shell find $(COV_TESTS_DIR) -type d -name '*_test_*' | head -n 1)
# export COV_RUNS = $(shell find $(COV_TESTS_DIR) -type d -name '*_test_*')
export COV_RUNS = $(shell find $(COV_TESTS_DIR) -type d -name '*_test_*')
export COV_MERGED_DIR = $(DV_COV_DIR)/merged
export COV_REPORT_DIR := $(TB_HOME)/cov_report
RISCX_LOG = $(wildcard $(DV_OUT_DIR)/risc-x_sim/*.log)

log2csv:
	@for log_file in $(RISCX_LOG); do \
		csv_file=$$(echo $$log_file | sed 's/\.log$$/\.csv/') ; \
		python3 -c "import riscx_log_to_trace_csv as l2t; l2t.process_riscx_sim_log('$$log_file', '$$csv_file', 1)"; \
	done

cov-collect:
	@$(DV_COV_CMD) --output $(DV_COV_DIR) --dir $(DV_OUT_DIR)/risc-x_sim \
		--core=risc-x --simulator xlm --noclean

cov-collect-spike:
	@$(DV_COV_CMD) --output $(DV_COV_DIR) --dir $(DV_OUT_DIR)/spike_sim \
		--iss=spike --simulator xlm --noclean

cov-merge: $(COV_TESTS_DIR)
	@imc -exec cov_merge.tcl

cov-report: $(COV_MERGED_DIR)
	@imc -exec cov_script.tcl

cov-full: log2csv cov-collect cov-merge cov-report

##########################################################################################################################

clean-sim:
	rm -rf xcelium.d xrun* .simvision .symbol* waves* jgproject *.log *.diag trace* $(DV_OUT_DIR)/*_sim/ $(DV_OUT_DIR)/*.log

clean-asm:
	rm -rf $(DV_OUT_DIR)/asm_test/

clean-cov:
	rm -rf imc.* cov_work/ mdv.log $(DV_COV_DIR) $(COV_REPORT_DIR)

clean-generator:
	rm -rf $(DV_OUT_DIR)

clean: clean-sim clean-asm clean-cov clean-generator

##########################################################################################################################
# From this point everything is just for testing, do not use these 

SPIKE_LOG := $(wildcard $(DV_OUT_DIR)/spike_sim/*.log)
spike_full_csv:
	@for log_file in $(SPIKE_LOG); do \
		csv_file=$$(echo $$log_file | sed 's/\.log$$/\.csv/') ; \
		python3 -c "import run; run.process_spike_sim_log('$$log_file', '$$csv_file', 1)"; \
	done

test:
	@echo $(DV_ALL_SIM_TESTS)
	@for x in $(DV_ALL_SIM_TESTS); do \
		echo $$x ; \
	done
	