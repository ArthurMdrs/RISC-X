.globl main

.text
main:
	# Load initial values
    addi x1, x0, 1      # x1 will hold the wdata
    addi x31, x0, 0     # x31 will hold the waddr
    addi x30, x0, 1024  # x30 should be the mem size

loop:
    sw x1, 0(x31)
    addi x31, x31, 4
    addi x1, x1, 1
    bne x31, x30, loop

    # Read all the values back
    addi x31, x0, 0
loop_read:
    lw x1, 0(x31)
    srli x2, x31, 2     # x2 = x31 / 4
    addi x2, x2, 1		# x2 = 1 + x31 / 4
    bne x1, x2, error
    addi x31, x31, 4
    bne x31, x30, loop_read
    j finnish

error:
    sw x30, 0(x0)

finnish:
