# SVA = +define+SVA_ON=1

export RTL_HOME := $(abspath $(shell pwd)/../../rtl)
export RVFI_HOME := $(abspath $(shell pwd)/../../fv)
export RVVI_HOME := $(abspath $(shell pwd)/../rvvi)
export TB_HOME := $(abspath $(shell pwd))

DV_OUT_DIR := $(TB_HOME)/mytest
DV_FILE_LIST := $(RISCV_DV_ROOT)/files.f
DV_GEN_TEST := riscv_instr_base_test
DV_NUM_TESTS := 1
DV_RISCX_TARGET := $(TB_HOME)/riscx_target
DV_ISS_YAML := $(TB_HOME)/iss.yaml
DV_SIM_TEST := riscv_arithmetic_basic_test
DV_RUN_COMMON_FLAGS := --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) \
					   --simulator xlm --noclean \
					   --custom_target $(DV_RISCX_TARGET) --isa rv32i_zicsr_zifencei --mabi ilp32 

PROGS_PATH := $(abspath $(shell pwd)/../programs)
PROG := 
PLUS_ARG := +progs_path=$(PROGS_PATH)
ifeq ($(strip $(PROG)),)
	PLUS_ARG +=
else
	PLUS_ARG += +prog=$(PROG)
endif

SEED = 
INPUT = -input restore.tcl

ELF=/home/pedro.medeiros/Tools/riscv-dv/mytest/asm_test/$(DV_SIM_TEST)_0.o

XRUN_COMMON_FLAGS := -64bit -sv -uvm -uvmhome $(UVMHOME)
XRUN_COMP_FLAGS := $(XRUN_COMMON_FLAGS) -elaborate -l $(DV_OUT_DIR)/compile.log -xmlibdirpath $(DV_OUT_DIR)
XRUN_SIM_FLAGS := $(XRUN_COMMON_FLAGS) +define+SIM -svseed $(SEED)
FILES := -f file_list.f
SIM_TOP := -top riscv_dv_tb

DEPS := $(RVVI_HOME)/rvviTrace.sv $(RVFI_HOME)/rvfi_macros.vh

run: $(DEPS) sim

sim: $(DEPS)
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

gui: $(DEPS)
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) $(PLUS_ARG) \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED) -gui $(INPUT)

$(RVFI_HOME)/rvfi_macros.vh: 
	@curl -L -o $(RVFI_HOME)/rvfi_macros.vh https://raw.githubusercontent.com/ArthurMdrs/riscv-formal/cv32e40p_v1.8.2/checks/original_checks/rvfi_macros.vh

$(RVVI_HOME)/rvviTrace.sv:
	@curl -L -o $(RVVI_HOME)/rvviTrace.sv https://raw.githubusercontent.com/riscv-verification/RVVI/main/source/host/rvvi/rvviTrace.sv

clean:
	rm -rf xcelium.d xrun* .simvision .symbol* waves* jgproject *.log trace* mytest
	
rars:
	python3 run_rars.py $(PROGS_PATH) $(PROG)

elf2hex:
	@python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt

sim-elf: $(DEPS)
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +check_regs=0 +check_mem=0 +print_trace=1 \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

sim-elf-gui: $(DEPS)
	python3 elf2hex.py $(ELF) $(PROGS_PATH)/out_prog.txt
	xrun -64bit -sv +define+SIM $(SVA) $(SIM_TOP) $(FILES) -gui $(INPUT) \
		 +progs_path=$(PROGS_PATH) +prog=out +text_start=8000_0000 \
		 +check_regs=0 +check_mem=0 +print_trace=1 \
		 -timescale 1ns/1ps -access +rwc -svseed $(SEED)

##########################################################################################################################

# compile-instr-generator:
# 	xrun $(XRUN_COMP_FLAGS) +incdir+riscx_target +incdir+$(RISCV_DV_ROOT)/user_extension \
# 		-f $(DV_FILE_LIST) -top riscv_instr_gen_tb_top

# run-instr-generator: $(DV_OUT_DIR)
# 	xrun $(XRUN_SIM_FLAGS) -R -xmlibdirpath $(DV_OUT_DIR) +UVM_TESTNAME=$(DV_GEN_TEST) +num_of_tests=$(DV_NUM_TESTS)

##########################################################################################################################

# compile-instr-generator:
# 	cd $(RISCV_DV_ROOT) && python3 run.py --co --output $(DV_OUT_DIR) \
# 		--custom_target $(DV_RISCX_TARGET) --simulator xlm

# gen-and-compile-asm:
# 	cd $(RISCV_DV_ROOT) && python3 run.py --test=$(DV_SIM_TEST) --so --output $(DV_OUT_DIR) \
# 		--custom_target $(DV_RISCX_TARGET) --isa rv32i_zicsr_zifencei --mabi ilp32 \
# 		--iss_yaml $(DV_ISS_YAML) --simulator xlm \
# 		--steps gen,gcc_compile --noclean

# dv-sim:
# 	cd $(RISCV_DV_ROOT) && python3 run.py --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) \
# 		--custom_target $(DV_RISCX_TARGET) --isa rv32i_zicsr_zifencei --mabi ilp32 \
# 		--iss_yaml $(DV_ISS_YAML) --simulator xlm --iss=risc-x,spike \
# 		--steps iss_sim --noclean

# dv-cmp:
# 	cd $(RISCV_DV_ROOT) && python3 run.py --test=$(DV_SIM_TEST) --output $(DV_OUT_DIR) \
# 		--custom_target $(DV_RISCX_TARGET) --isa rv32i_zicsr_zifencei --mabi ilp32 \
# 		--iss_yaml $(DV_ISS_YAML) --simulator xlm --iss=risc-x,spike \
# 		--steps iss_cmp --noclean 

##########################################################################################################################

compile-instr-generator:
	python3 run_mod.py --co --output $(DV_OUT_DIR) \
		--custom_target $(DV_RISCX_TARGET) --simulator xlm

gen-and-compile-asm:
	python3 run_mod.py $(DV_RUN_COMMON_FLAGS) --so --steps gen,gcc_compile

sim-dv:
	python3 run_mod.py $(DV_RUN_COMMON_FLAGS) --steps iss_sim \
		--iss_yaml $(DV_ISS_YAML) --iss=risc-x,spike

compare:
	python3 run_mod.py $(DV_RUN_COMMON_FLAGS) --steps iss_cmp \
		--iss=risc-x,spike
	
testing:
	python3 run_mod.py --test=$(DV_SIM_TEST) --custom_target $(DV_RISCX_TARGET) --isa rv32i_zicsr_zifencei \
		--mabi ilp32 --iss_yaml $(DV_ISS_YAML) --simulator xlm --output $(DV_OUT_DIR) --steps gen,gcc_compile,iss_sim
	