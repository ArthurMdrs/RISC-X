.globl main

.section .text

main:
    # x4 will be the base addr for .data
    la x4, .data
    
	# Load initial values
    addi x1, x0, 1      # x1 will hold the wdata

    addi x2, x0, 2
    addi x3, x0, 1

    # Test beq
    beq x1, x2, branch1
    sw x1, 0(x4)            # This should happen
    beq x1, x3, branch1
    sw x1, 4(x4)            # This should not happen

branch1:
    # Test bne
    bne x1, x3, branch2
    sw x1, 8(x4)            # This should happen
    bne x1, x2, branch2
    sw x1, 12(x4)           # This should not happen

branch2:
    # Test blt
    addi x2, x0, -1         # Make x2 negative for signed comparison
    blt x1, x3, branch3
    sw x1, 16(x4)           # This should happen
    blt x2, x1, branch3
    sw x1, 20(x4)           # This should not happen

branch3:
    # Test bge
    bge x2, x1, branch4
    sw x1, 24(x4)           # This should happen
    bge x1, x2, branch4
    sw x1, 28(x4)           # This should not happen

branch4:
    # Test bltu
    bltu x2, x1, branch5
    sw x1, 32(x4)           # This should happen
    bltu x1, x2, branch5
    sw x1, 36(x4)           # This should not happen

branch5:
    # Test bgeu
    bgeu x1, x2, branch6
    sw x1, 40(x4)           # This should happen
    bgeu x2, x1, branch6
    sw x1, 44(x4)           # This should not happen

branch6:
    nop
    lw x5, 0(x4)
    lw x6, 4(x4)
    lw x7, 8(x4)
    lw x8, 12(x4)
    lw x9, 16(x4)
    lw x10, 20(x4)
    lw x11, 24(x4)
    lw x12, 28(x4)
    lw x13, 32(x4)
    lw x14, 36(x4)
    lw x15, 40(x4)
    lw x16, 44(x4)
    
    ecall
