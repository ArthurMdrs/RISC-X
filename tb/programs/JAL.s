.include "init.s"

.section .text
.globl main
main:
    # x6 will be the base addr for .data
    la x6, .data
    
	# Load initial values
    addi x2, zero, 1

    # Test jal
	jal ra, target1
    addi x4, zero, 2
    sw x4, 44(x6)
	jalr ra, ra, 4

target1:
    addi x3, zero, 3
    sw x3, 40(x6)
    # Test jalr
	jalr ra

	nop
    addi ra, zero, 1
    sw ra, 48(x6)
    sw gp, 52(x6)
    
    ecall
    nop
    j _exit
	