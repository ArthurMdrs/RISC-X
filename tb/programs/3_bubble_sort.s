# The program below is based on https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main

.include "init.s"

.section .text
.globl main
main:
        addi x1, x0, 0
        addi x2, x0, 50
        addi x3, x0, 100
        addi x4, x0, 2
        la x5, .data
makeseq:
        sw x3, 0(x5)
        sub x3, x3, x4
        addi x5, x5, 4
        addi x1, x1, 1
        blt x1, x2, makeseq
        addi x5, x5, -4
        addi x1, x0, 1
ext:
        la x6, .data
        addi x7, x0, 0

inf:
        lw x8, 0(x6)
        lw x9, 4(x6)
        blt x9, x8, swap
back:
        addi x6, x6, 4
        blt x6, x5, inf
        beq x7, x1, ext
        jal x11, end
swap:
        addi x7, x0, 1
        sw x9, 0(x6)
        sw x8, 4(x6)
        jal x10, back
end:
    
    ecall
    nop
    j _exit
