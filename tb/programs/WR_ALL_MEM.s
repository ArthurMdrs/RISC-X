.include "init.s"

.section .text
.globl main
main:
	# Load initial values
    addi x1, x0, 1      # x1 will hold the wdata
    la x15, .data       # x15 will hold the addr of .data
    mv x31, x15         # x31 will hold the waddr
    addi x30, x15, 1024  # 1024 should be the mem size

loop:
    sw x1, 0(x31)
    addi x31, x31, 4
    addi x1, x1, 1
    bne x31, x30, loop

    # Read all the values back
    mv x31, x15
loop_read:
    lw x1, 0(x31)
    srli x2, x31, 2     # x2 = x31 / 4
    addi x2, x2, 1		# x2 = 1 + x31 / 4
    bne x1, x2, error
    addi x31, x31, 4
    bne x31, x30, loop_read
    j finish

error:
    sw x30, 0(x15)

finish:
    slli gp, sp, 10
    
    ecall
    nop
    j _exit
