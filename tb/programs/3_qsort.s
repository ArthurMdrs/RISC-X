# The program below was copied from https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main
        addi x1, x0, 0
        addi x2, x0, 50
        addi x3, x0, 100
        addi x4, x0, 2
        addi x5, x0, 0
makeseq:
        sw x3, 0(x5)
        sub x3, x3, x4
        addi x5, x5, 4
        addi x1, x1, 1
        blt x1, x2, makeseq
        addi x5, x5, -4
        addi x7, x0, 1000
        addi x12, x0, 1
        addi x11, x0, 0
        add x8, x0, x0
        add x9, x5, x0
quickSort:
        blt x8, x9, quickSortif1action
        jal x0, quickSortend
quickSortif1action:
        add x2, x8, x0
        add x3, x9, x0
        jal x0, qsort
quickSortbackpoint1:
        add x10, x1, x0
        sw x11, 0(x7)
        addi x7, x7, -4
        sw x8, 0(x7)
        addi x7, x7, -4
        sw x9, 0(x7)
        addi x7, x7, -4
        sw x10, 0(x7)
        addi x7, x7, -4
        addi x11, x0, 1
        add x8, x8, x0
        addi x9, x10, -4
        jal x0, quickSort
quickSortbackpoint2:
        addi x7, x7, 4
        lw x10, 0(x7)
        addi x7, x7, 4
        lw x9, 0(x7)
        addi x7, x7, 4
        lw x8, 0(x7)
        addi x7, x7, 4
        lw x11, 0(x7)
        sw x11, 0(x7)
        addi x7, x7, -4
        sw x8, 0(x7)
        addi x7, x7, -4
        sw x9, 0(x7)
        addi x7, x7, -4
        sw x10, 0(x7)
        addi x7, x7, -4
        addi x11, x0, 2
        addi x8, x10, 4
        add x9, x9, x0
        jal x0, quickSort
quickSortbackpoint3:
        addi x7, x7, 4
        lw x10, 0(x7)
        addi x7, x7, 4
        lw x9, 0(x7)
        addi x7, x7, 4
        lw x8, 0(x7)
        addi x7, x7, 4
        lw x11, 0(x7)
quickSortend:
        beq x11, x0, programend
        beq x11, x12, quickSortbackpoint2
        jal x0, quickSortbackpoint3
qsort:
        add x1, x0, x2
qsortloop1:
        lw x4, 0(x1)
        lw x6, 0(x3)
        blt x6, x4, qsortloop1break
        beq x3, x1, qsortloop1break
qsortloop1action:
        addi x3, x3, -4
        jal x0, qsortloop1
qsortloop1break:
        beq x1, x3, qsortbreak
        jal x0, qsortif1
qsortif1action:
        sw x6, 0(x1)
        sw x4, 0(x3)
        add x1, x0, x3
        jal x0, qsortloop2
qsortif1:
        blt x6, x4, qsortif1action
qsortloop2:
        lw x5, 0(x2)
        lw x4, 0(x1)
        blt x4, x5, qsortloop2break
        beq x1, x2, qsortloop2break
qsortloop2action:
        addi x2, x2, 4
        jal x0, qsortloop2
qsortloop2break:
        beq x1, x2, qsortbreak
        jal x0, qsortif2
qsortif2action:
        sw x5, 0(x1)
        sw x4, 0(x2)
        add x1, x0, x2
        jal x0, qsortwhile
qsortif2:
        blt x4, x5, qsortif2action
qsortwhile:
        jal x0, qsortloop1
qsortbreak:
        jal x0, quickSortbackpoint1
programend:
    
    ecall
