void init() {
asm volatile (
    ".section .text\n"
    ".globl _start\n"
    "_start:\n"
    "    la t0, mtvec_handler\n"
    "    csrw mtvec, t0\n"
    "    j main\n"
    
    "write_tohost:\n"
    "    la t0, tohost\n"
    "    li t1, 1\n"
    "    sw t1, 0(t0)\n"

    "_exit:\n"
    "    j write_tohost\n"

    "instr_end:\n"
    "    nop\n"
        
    ".pushsection .tohost,\"aw\",@progbits; " 
    ".align 6; .global tohost; tohost: .dword 0; .size tohost, 8;\n"
    ".align 6; .global fromhost; fromhost: .dword 0; .size tohost, 8;\n"
    ".popsection;\n"

    ".align 8\n"
    ".text\n"
    "mtvec_handler:\n"
    "    j write_tohost\n"
);
}
