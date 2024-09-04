# The program below is based on https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main

.include "init.s"

.section .text
.globl main
main:
    addi x31, x0, 1
    addi x30, x0, 255
    add x29, x31, x2
    sub x28, x29, x1
    and x5, x31, x2
    or x6, x31, x2
    xor x7, x31, x2
    addi x8, x0, 0
    addi x9, x0, 7
    addi x10, x0, 1
    addi x11, x0, 1
loop:
    sll x10, x10, x11
    addi x8, x8, 1
    blt x8, x9, loop
    addi x9, x9, 7
    add x12, x10, x0
loop2:
    srl x10, x12, x11
    addi x8, x8, 1
    blt x8, x9, loop2
    #addi x13, x0, 0
    la x13, .data
    sw x0, 0(x13)
    addi x13, x13, 4
    sw x31, 0(x13)
    addi x13, x13, 4
    sw x30, 0(x13)
    addi x13, x13, 4
    sw x29, 0(x13)
    addi x13, x13, 4
    sw x28, 0(x13)
    addi x13, x13, 4
    sw x5, 0(x13)
    addi x13, x13, 4
    sw x6, 0(x13)
    addi x13, x13, 4
    sw x7, 0(x13)
    addi x13, x13, 4
    sw x8, 0(x13)
    addi x13, x13, 4
    sw x9, 0(x13)
    addi x13, x13, 4
    sw x10, 0(x13)
    addi x13, x13, 4
    sw x11, 0(x13)
    addi x13, x13, 4
    sw x12, 0(x13)
    addi x13, x13, 4
    addi x14, x0, 4
    sub x13, x13, x14
    lw x0, 0(x13)
    sub x13, x13, x14
    lw x31, 0(x13)
    sub x13, x13, x14
    lw x30, 0(x13)
    sub x13, x13, x14
    lw x29, 0(x13)
    sub x13, x13, x14
    lw x28, 0(x13)
    sub x13, x13, x14
    lw x5, 0(x13)
    sub x13, x13, x14
    lw x6, 0(x13)
    sub x13, x13, x14
    lw x7, 0(x13)
    sub x13, x13, x14
    lw x8, 0(x13)
    sub x13, x13, x14
    lw x9, 0(x13)
    sub x13, x13, x14
    lw x10, 0(x13)
    sub x13, x13, x14
    lw x11, 0(x13)
    sub x13, x13, x14
    lw x12, 0(x13)
    jal x15, loop3
loop3:
    ecall
