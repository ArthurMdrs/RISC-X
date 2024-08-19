

.align 8
mtvec_handler:
    j write_tohost
    mret


.section .data
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
