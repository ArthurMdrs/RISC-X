.globl main

.text
main:
	# Load initial values
    addi x2, zero, 1

    # Test jal
	jal ra, target1
    addi x4, zero, 2
    sw x4, 44(zero)
	jalr ra, ra, 4

target1:
    addi x3, zero, 3
    sw x3, 40(zero)
    # Test jalr
	jalr ra

	nop
    addi ra, zero, 1
    sw ra, 48(zero)
    sw gp, 52(zero)
	