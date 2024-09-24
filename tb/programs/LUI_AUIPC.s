.include "init.s"

.section .text
.globl main
main:
    # t3 will be the base addr for .data
    la t3, .data
    
	# Use lui to load values
    lui t0, 0x10101
    ori t0, t0, 0x101
    lui t1, 0xFFFFF
    ori t1, t1, -4
	lui s0, 0xc7a29
	
	# Test auipc
	auipc t2, 0xABCDE
	auipc gp, 0xFEDCB
	auipc sp, 0x23456
    
    # Store in memory
    sw t0, 0(t3)
    sw t1, 4(t3)
    sw t2, 8(t3)
    sw s0, 20(t3)
    sw gp, 28(t3)
    sw sp, 100(t3)
    
    ecall
    nop
    j _exit
