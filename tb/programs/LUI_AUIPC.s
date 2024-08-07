.globl main

.text
main:
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
    sw t0, 0(x0)
    sw t1, 4(x0)
    sw t2, 8(x0)
    sw s0, 20(x0)
    sw gp, 28(x0)
    sw sp, 100(x0)
    
    ecall