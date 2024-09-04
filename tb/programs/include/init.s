
.section .text

.globl _start
_start:
    # li t0, 0x40001104
    # csrw misa, t0
    la t0, mtvec_handler
    csrw mtvec, t0
    # la t0, init
    # csrw mepc, t0
    # li t0, 0x1800
    # csrw mstatus, t0
    # li t0, 0x0
    # csrw mie, t0
    j main
    # mret

# init:
#     li ra, 0x0
#     li sp, 0x80000000
#     li gp, 0x80000000
#     li tp, 0xbbbf6de1





# Define write_tohost, which tells Spike to terminate simulation
write_tohost:
    la t0, tohost
    li t1, 1
    sw t1, 0(t0)

_exit:
    j write_tohost

instr_end:
    nop


.section .data

# Define tohost and fromhost addresses
.pushsection .tohost,"aw",@progbits;  
.align 6; .global tohost; tohost: .dword 0; .size tohost, 8;
.align 6; .global fromhost; fromhost: .dword 0; .size tohost, 8;
.popsection;

# Define trap handlers
.align 8
.text
mtvec_handler:
    j write_tohost
    # mret

# Do we need this?
# .section .user_stack,"aw",@progbits;
# .align 2
# user_stack_start:
# .rept 4999
# .4byte 0x0
# .endr
# user_stack_end:
# .4byte 0x0

# kernel_instr_end: nop
# .section .kernel_stack,"aw",@progbits;
# .align 2
# kernel_stack_start:
# .rept 3999
# .4byte 0x0
# .endr
# kernel_stack_end:
# .4byte 0x0
