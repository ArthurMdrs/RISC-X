.globl main

.text
main:
	# Use lui to load values
    lui t0, 0x10101
    ori t0, t0, 0x101
    lui t1, 0xFFFFF
    ori t1, t1, -4
	lui s0, 0x00002
	
	# Test auipc
	auipc t2, 0xABCDE
    
    # Store in memory
    sw t0, 0(s0)
    sw t1, 4(s0)
    sw t2, 8(s0)