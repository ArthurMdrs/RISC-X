# CORE-X Verification

First, you will need to install Spike ISA simulator and Google's RISCV-DV.

The following environment variables must be set:

- UVMHOME: Root of UVM library (not necessary?)
- RISCV_DV_ROOT: Root of Google's RISCV-DV repository
- RISCV_GCC: path to your RISC-V gcc executable (ex: /opt/riscv/bin/riscv32-unknown-linux-gnu-gcc)
- SPIKE_PATH: path to your Spike directory (ex: /opt/riscv/bin)

Currently, only Cadence's tools are supported (xrun for simulation and IMC for coverage).

Flow:
```Shell
make compile-instr-generator
make gen-sim-cmp DV_SIM_TEST=<test_name>
make cov-full
```

The target `compile-instr-generator` will compile Google's RISCV-DV instruction generator. This target need to be executed only once. `gen-sim-cmp` performs various steps. It will run the generator to generate the assembly tests; then it will simulate said tests on both the reference model (ISS simulator, currently only Spike is supported) and the core; lastly, it will covert the logs to csv files and compare them. Currently, all the output files are send to the folder `mytest`. In this folder, you will find the file `iss_regr.log` containing the results of the comparison. At the end, there should be something like "2 PASSED, 0 FAILED".

The target `cov-full` will collect coverage data from the core's log and save it to `mytest/cov/default`. It will merge all runs is that folder, in case there is more than 1, and then it will generate a HTML report with that coverage in the folder `cov_report`.

Replace <test_name> for one of the Google's RISCV-DV base tests (list below). 

>- riscv_arithmetic_basic_test
>
>   Arithmetic instruction test, no load/store/branch instructions

>- riscv_rand_instr_test
>
>   Random instruction stress test

>- riscv_jump_stress_test
>
>   Stress back-to-back jump instruction test

>- riscv_loop_test
>
>   Random instruction stress test

>- riscv_rand_jump_test
>
>   Jump among large number of sub-programs, stress testing iTLB operations.

>- riscv_mmu_stress_test
>
>   Test with different patterns of load/store instructions, stress test MMU

>- riscv_no_fence_test
>
>   Random instruction with FENCE disabled, used to test processor pipeline with less stall/flush operations caused by FENCE instruction.

>- riscv_illegal_instr_test
>
>   Illegal instruction test, verify the processor can detect illegal instruction and handle corresponding exception properly. An exception handling routine is designed to resume execution after illegal instruction exception.

>- riscv_ebreak_test
>
>   Random instruction test with ebreak instruction enabled. Debug mode is not enabled for this test, processor should raise ebreak exception.

>- riscv_ebreak_debug_mode_test
>
>   Ebreak instruction test with debug mode enabled.

>- riscv_full_interrupt_test
>
>   Random instruction test with complete interrupt handling

>- riscv_csr_test
>
>   Test all CSR instructions on all implemented CSR registers

>- riscv_unaligned_load_store_test
>
>   Unaligned load/store test

## Current state

All tests from the list above, up to riscv_no_fence_test, passed.

## Known issues

- Coverage collection is not working properly for RISC-X.
- Bugs when running riscv_illegal_instr_test.