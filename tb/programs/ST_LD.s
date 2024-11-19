.include "init.s"

.section .text
.globl main
main:
    # x22 will be the base addr for .data
    la x22, .data
    
	# Load initial values
    addi x1, x0, 3
    addi x2, x0, 9
    
    # Test the OP instructions
    add x2, x1, x2
    sub x3, x1, x2
    xor x4, x2, x3
    or x5, x3, x4
    and x6, x5, x4
    sll x7, x6, x1
    srl x8, x7, x1
    sra x9, x7, x1
    slt x10, x8, x7
    sltu x11, x7, x8

    # Test STORE instructions
    sw x7, 128(x22)
    sh x7, 132(x22)
    sb x7, 136(x22)
    sb x1, 135(x22)
    sh x9, 138(x22)
    
    # Test LOAD instructions
    lw x12, 128(x22)
    lh x13, 128(x22)
    lhu x14, 128(x22)
    lb x15, 128(x22)
    lbu x16, 128(x22)
    
    lw x17, 132(x22)
    lh x18, 132(x22)
    lhu x19, 132(x22)
    lb x20, 132(x22)
    lbu x21, 132(x22)
    
    # Test LOAD stalls
    lw x12, 132(x22)
    add x2, x12, x2
    xor x4, x2, x12
    sltu x11, x12, x2
    
    lhu x19, 136(x22)
    and x6, x5, x19
    addi x2, x19, 9
    sra x9, x19, x2

    # Store the regs to mem
    sw x0, 0(x22)
    sw x1, 4(x22)
    sw x2, 8(x22)
    sw x3, 12(x22)
    sw x4, 16(x22)
    sw x5, 20(x22)
    sw x6, 24(x22)
    sw x7, 28(x22)
    sw x8, 32(x22)
    sw x9, 36(x22)
    sw x10, 40(x22)
    sw x11, 44(x22)
    sw x12, 48(x22)
    sw x13, 52(x22)
    sw x14, 56(x22)
    sw x15, 60(x22)
    sw x16, 64(x22)
    sw x17, 68(x22)
    sw x18, 72(x22)
    sw x19, 76(x22)
    sw x20, 80(x22)
    sw x21, 84(x22)
    sw x22, 88(x22)
    sw x23, 92(x22)
    sw x24, 96(x22)
    sw x25, 100(x22)
    sw x26, 104(x22)
    sw x27, 108(x22)
    sw x28, 112(x22)
    sw x29, 116(x22)
    sw x30, 120(x22)
    sw x31, 124(x22)
    
    ecall
    nop
    j _exit
