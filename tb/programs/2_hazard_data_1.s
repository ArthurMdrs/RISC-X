# The program below is based on https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main

.include "init.s"

.section .text
.globl main
main:
    la x11, .data
    addi x1, x0, 0
    addi x2, x0 ,1
    addi x3, x0 ,2
    addi x4, x0, 3
    sw x4, 0(x11)
    add x5, x4, x3
    add x6, x5, x3
    add x7, x4, x5
    add x8, x7, x6
    lw x9, 0(x11)
    add x10, x9, x8
    
    ecall
    nop
    j _exit
