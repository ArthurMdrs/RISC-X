
.section .text

.globl _start
_start:
    la x9, mtvec_handler
    csrw 0x305, x9 # MTVEC
    j main

write_tohost:
    li t0, 1
    #li t1, 4
    #sw zero, tohost, t1
    sw t0, tohost, zero
    j write_tohost

