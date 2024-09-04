# The program below is based on https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main

.include "init.s"

.section .text
.globl main
main:
        addi x1, x0, 1
        addi x2, x0, 10
        addi x3, x0, 1
loop:
        addi x3, x3, 1
        la x4, .data
        sw x3, 0(x4)
        add x0, x0, x0
        lw x1, 0(x4)
        blt x1, x2, loop
    
    nop
    nop
    ecall
    nop
    j _exit

