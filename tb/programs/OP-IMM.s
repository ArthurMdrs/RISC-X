.include "init.s"

.section .text
.globl main
main:
    # x10 will be the base addr for .data
    la x10, .data
    
    # Test the OP-IMM instructions
    addi x1, x0, -1
    xori x2, x1, 0x7ff
    ori x3, x2, 0x00f
    andi x4, x3, 0x00f
    slli x5, x3, 8
    srli x6, x3, 8
    srai x7, x3, 8
    slti x8, x7, 0x7ff
    sltiu x9, x7, 0x7ff

	# Store the regs to mem for dumping
    sw x0, 0(x10)
    sw x1, 4(x10)
    sw x2, 8(x10)
    sw x3, 12(x10)
    sw x4, 16(x10)
    sw x5, 20(x10)
    sw x6, 24(x10)
    sw x7, 28(x10)
    sw x8, 32(x10)
    sw x9, 36(x10)
    sw x10, 40(x10)
    sw x11, 44(x10)
    sw x12, 48(x10)
    sw x13, 52(x10)
    sw x14, 56(x10)
    sw x15, 60(x10)
    sw x16, 64(x10)
    sw x17, 68(x10)
    sw x18, 72(x10)
    sw x19, 76(x10)
    sw x20, 80(x10)
    sw x21, 84(x10)
    sw x22, 88(x10)
    sw x23, 92(x10)
    sw x24, 96(x10)
    sw x25, 100(x10)
    sw x26, 104(x10)
    sw x27, 108(x10)
    sw x28, 112(x10)
    sw x29, 116(x10)
    sw x30, 120(x10)
    sw x31, 124(x10)
    
    ecall
    nop
    j _exit
