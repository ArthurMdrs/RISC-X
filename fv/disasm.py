#!/usr/bin/env python3

from Verilog_VCD.Verilog_VCD import parse_vcd # type: ignore
from os import system
from sys import argv

rvfi_valid = None
rvfi_order = None
rvfi_insn = None

for netinfo in parse_vcd(argv[1]).values():
    for net in netinfo['nets']:
        # if net["hier"] == "rvfi_testbench.wrapper" and (net["name"] == "rvfi_valid" or net["name"] == "rvfi_order[0]"):
        if net["hier"] == "rvfi_testbench.wrapper" and (net["name"].startswith("rvfi_valid")):
            rvfi_valid = netinfo['tv']
        # if net["hier"] == "rvfi_testbench.wrapper" and (net["name"] == "rvfi_order" or net["name"] == "rvfi_order[63:0]"):
        if net["hier"] == "rvfi_testbench.wrapper" and (net["name"].startswith("rvfi_order")):
            rvfi_order = netinfo['tv']
        # if net["hier"] == "rvfi_testbench.wrapper" and (net["name"] == "rvfi_insn" or net["name"] == "rvfi_insn[31:0]"):
        if net["hier"] == "rvfi_testbench.wrapper" and (net["name"].startswith("rvfi_insn")):
            rvfi_insn = netinfo['tv']

assert(rvfi_valid != None)
assert(rvfi_order != None)
assert(rvfi_insn != None)

# print(rvfi_valid)
# for x in rvfi_valid: print(x)

# Expect a list of (int, str) holding time values and signal values
nret = len(rvfi_valid[0][1])
# print(nret)

time_vals = []
valid_time_vals = []
order_time_vals = []
insn_time_vals = []
    
for val in rvfi_valid:
    valid_time_vals.append(val[0])
    if val[0] not in time_vals: time_vals.append(val[0])
for val in rvfi_order:
    order_time_vals.append(val[0])
    if val[0] not in time_vals: time_vals.append(val[0])
for val in rvfi_insn:
    insn_time_vals.append(val[0])
    if val[0] not in time_vals: time_vals.append(val[0])

time_vals.sort()
time_start = min(time_vals)
time_end   = max(time_vals)

def fill_time_slots (time_vals, unfilled_slots, tuple_vec):
    new_vec = []
    prev_val = ""
    for time in time_vals:
        if time in unfilled_slots:
            idx = unfilled_slots.index(time)
            new_vec.append(tuple_vec[idx])
            prev_val = tuple_vec[idx][1]
        else: 
            new_vec.append([time, prev_val])
    return new_vec

rvfi_valid = fill_time_slots(time_vals, valid_time_vals, rvfi_valid)
rvfi_order = fill_time_slots(time_vals, order_time_vals, rvfi_order)
rvfi_insn  = fill_time_slots(time_vals, insn_time_vals , rvfi_insn )
# print(rvfi_valid)
# print(rvfi_insn)

assert len(rvfi_valid) == len(rvfi_order)
assert len(rvfi_valid) == len(rvfi_insn)

prog = list()

# print(len(rvfi_order[0][1]))
for tv_valid, tv_order, tv_insn in zip(rvfi_valid, rvfi_order, rvfi_insn):
    # print(tv_valid, tv_order, tv_insn)
    # print(tv_order[1][127])
    for ch in range(nret):
        if tv_valid[1][ch] == '1':
            prog.append((int(tv_order[1][ch*64:ch*64+64], 2), int(tv_insn[1][ch*32:ch*32+32], 2)))
# for x in prog: print(x)

with open("disasm.s", "w") as f:
    for tv_order, tv_insn in sorted(prog):
        if tv_insn & 3 != 3 and tv_insn & 0xffff0000 == 0:
            print(".hword 0x%04x # %d" % (tv_insn, tv_order), file=f)
        else:
            print(".word 0x%08x # %d" % (tv_insn, tv_order), file=f)

# system("riscv32-corev-elf-gcc -march=rv32imc_zicsr_zfinx_xcvalu_xcvbi_xcvbitmanip_xcvhwlp_xcvmac_xcvmem_xcvsimd -c disasm.s")
# system("riscv32-corev-elf-objdump -D -M numeric,no-aliases -j .text disasm.o")

system("riscv32-unknown-linux-gnu-gcc -march=rv32imfc_zicsr -mabi=ilp32 -c disasm.s")
system("riscv32-unknown-linux-gnu-objdump -D -M numeric,no-aliases -j .text disasm.o")

# multilib_defaults:
# march=rv32imafdc_zicsr_zifencei mabi=ilp32d