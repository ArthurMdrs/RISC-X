#!/bin/bash

isa=rv32idc_zicsr_zifencei
RISCV_PREFIX=riscv32-unknown-linux-gnu-

compile-c(){
    # Check if an argument is provided
    if [ -z "$1" ]; then
        echo "Usage: $0 compile-c <c_program>"
        exit 1
    fi
    
    elf="$1"
    
    echo "Compiling $1."
    
    OUT="${1%.*}.o"

    "${RISCV_GCC}" -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles \
        -T linker.ld "$1" -o "$OUT" -Wl,-Map=output.map \
        -march="$isa" -mabi=ilp32d
}

compile-asm(){
    # Check if an argument is provided
    if [ -z "$1" ]; then
        echo "Usage: $0 compile-asm <asm_program>"
        # echo "<asm_program> should be given without extension (i.e. prog not prog.s)"
        exit 1
    fi
    
    ASM_FILE="$1"
    
    echo "Compiling ${ASM_FILE}."
    
    OUT="${ASM_FILE%.*}.o"
    
    # Assemble initialization file and assembly program
    # riscv32-unknown-linux-gnu-as -o init.out init.s
    riscv32-unknown-linux-gnu-as -o "${ASM_FILE}.out" "${ASM_FILE}"
    
    # Link the object files to produce an ELF file
    # riscv32-unknown-linux-gnu-ld -T linker.ld -o "${OUT}" "${ASM_FILE}.out" init.out
    riscv32-unknown-linux-gnu-ld -T linker.ld -o "${OUT}" "${ASM_FILE}.out"
    
    # rm "${ASM_FILE}.out" init.out
    rm "${ASM_FILE}.out"
}

run-spike(){
    # Check if an argument is provided
    if [ -z "$1" ]; then
        echo "Usage: $0 run-spike <executable>"
        exit 1
    fi
    
    ELF="$1"
    
    echo "Running $ELF on Spike."

    spike --log-commits --isa="$isa" --misaligned -l "$ELF"
}

disasm(){
    # Check if an argument is provided
    if [ -z "$1" ]; then
        echo "Usage: $0 disasm <executable>"
        exit 1
    fi
    
    ELF="$1"
    
    echo "Disassembling $ELF."

    "${RISCV_OBJDUMP}" -d "${ELF}" 
}


main(){
    func_list=$(compgen -A function | grep -v -e '^which$' -e '^main$')
    # echo "Functions: ${func_list}"
    
    func="$1"
    arg="$2"
    
    # Check the arguments are provided
    if [ -z "$func" ]; then
        echo "Usage: $0 <function> <argument>"
        echo "Functions: $(echo "$func_list" | tr '\n' ' ')"
        exit 1
    fi
    
    # Check if provided function exists and execute it
    if echo "${func_list}" | grep -q "^${func}$"; then
        "$func" "$arg"
    else 
        echo "Unidentified function $func."
        echo "Functions: $($func_list | tr '\n' ' ')"
        exit 1
    fi
}

main "$@"