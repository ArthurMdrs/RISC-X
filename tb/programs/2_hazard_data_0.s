# The program below is based on https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main

.include "init.s"

.section .text
.globl main
main:
    addi x1, x0, 0
    addi x2, x0 ,1
    addi x3, x0 ,2
    addi x4, x0, 3
    add x5, x4, x3
    add x6, x5, x3
    add x7, x4, x5
    add x8, x7, x6
    
    ecall
    nop
    j _exit
