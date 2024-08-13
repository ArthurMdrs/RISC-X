import subprocess
from sys import argv
import os
import re
# from pathlib import Path

riscv_prefix = "riscv32-unknown-linux-gnu-"

def elf2hex(elf_file, out_file):
    print(f"Converting {elf_file} to {out_file}.")
    
    # Run the objdump command and capture the output
    result = subprocess.run([f'{riscv_prefix}objdump', '-d', elf_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Check for errors
    if result.returncode != 0:
        print("Error running objdump:", result.stderr)
        return
    
    # Read output and capture hex code of instructions
    output = result.stdout.decode('utf-8')
    out_str = ""
    # print(elf_file)
    # print(out_file)
    # print(output)
    for line in output.splitlines():
        parts = line.split()
        if len(parts) > 1 and parts[0].endswith(':') and all(c in '0123456789abcdef' for c in parts[1].lower()):
            hex_code = line.split()[1]
            out_str += hex_code + "\n"
        # print(line)
    # print(out_str)
    
    # Write output file
    with open(out_file, "w") as f:
        f.write(out_str)

def get_sections_info(elf_file, out_file):
    print(f"Getting sections from {elf_file}.")
    print(f"Saving to {out_file}.")
    
    # Run the objdump command and capture the output
    result = subprocess.run([f'{riscv_prefix}objdump', "-h", elf_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    # Check for errors
    if result.returncode != 0:
        print("Error running objdump:", result.stderr)
        return

    # Parse the output
    output = result.stdout.decode('utf-8')
    sections = []
    # for line in result.stdout.splitlines():
    for line in output.splitlines():
        # match = re.match(r"\s*\d+\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+", line)
        match = re.match(r"\s*\d+\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+2\*\*([\d]+)", line)
        if match:
            name = match.group(1)
            size = int(match.group(2), 16)
            start_addr = int(match.group(3), 16)
            end_addr = start_addr + size - 1
            file_offset = match.group(5)
            alignment = match.group(6)
            sections.append((name, size, start_addr, end_addr, file_offset, alignment))
    
    # Print the sections information
    out_str = ""
    # out_str += "Name,Start Addr,End Addr,Size\n"
    out_str += "Start_Addr,End_Addr,Size,Alignment\n"
    for name, size, start_addr, end_addr, file_offset, alignment in sections:
        # print(f"{name},{start_addr:08x},{end_addr:08x},{size:08x}")
        out_str += f"{name}\n{start_addr:08x},{end_addr:08x},{size:08x},{alignment}\n"
    # print(out_str)
    
    # Write output file
    with open(out_file, "w") as f:
        f.write(out_str)

def main():
    if (len(argv) == 1):
        assert False, "ELF file not provided!"
    elf_file = argv[1]
    function_sel = 0
    if (len(argv) == 2):    # Provided ELF file
        out_file = elf_file + ".txt"
    else:
        out_file = argv[2]
        if (len(argv) == 3):  # Provided ELF file and path for output
            out_file = argv[2]
        elif (len(argv) == 4):  # Provided function selection
            if not (argv[3] in ["0", "1"]):
                assert False, f"Select a function: 0, 1. You selected: {argv[3]}"
            function_sel = int(argv[3])
        else:
            assert False, "Too many arguments!"
    
    if os.path.isfile(out_file):
        print("Output file already exists. Deleting...")
        os.remove(out_file)
    if not os.path.isfile(os.path.abspath(elf_file)):
    # if not Path(elf_file).exists():
        print("Error converting ELF file. File does not exist! File path:")
        print(os.path.abspath(elf_file))
        return
    
    if function_sel == 0:
        elf2hex(elf_file, out_file)
    elif function_sel == 1:
        get_sections_info(elf_file, out_file)

if __name__ == "__main__":
    main()