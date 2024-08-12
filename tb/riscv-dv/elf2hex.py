import subprocess
from sys import argv
import os
# from pathlib import Path

riscv_prefix = "riscv32-unknown-linux-gnu-"

def elf2hex(elf_path, hex_path):
    print(f"Converting {elf_path} to {hex_path}.")
    result = subprocess.run([f'{riscv_prefix}objdump', '-d', elf_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    hex_output = ""
    # print(elf_path)
    # print(hex_path)
    # print(output)
    for line in output.splitlines():
        parts = line.split()
        if len(parts) > 1 and parts[0].endswith(':') and all(c in '0123456789abcdef' for c in parts[1].lower()):
            hex_code = line.split()[1]
            hex_output += hex_code + "\n"
        # print(line)
    # print(hex_output)
    with open(hex_path, "w") as f:
        f.write(hex_output)

def main():
    if (len(argv) == 1):
        assert False, "ELF file not provided!"
    if (len(argv) > 3):
        assert False, "Too many arguments!"
    elf_path = argv[1]
    if (len(argv) == 3):
        hex_path = argv[2]
    else:
        hex_path = elf_path + ".txt"
    if os.path.isfile(hex_path):
        print("Deleting existing HEX file.")
        os.remove(hex_path)
    if not os.path.isfile(os.path.abspath(elf_path)):
    # if not Path(elf_path).exists():
        print("Error converting ELF file. File does not exist! File path:")
        print(os.path.abspath(elf_path))
        return
    elf2hex(elf_path, hex_path)

if __name__ == "__main__":
    main()