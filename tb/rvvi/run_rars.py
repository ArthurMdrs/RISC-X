# from os import system
import os
from sys import argv

def run_rars(progs_roots, prog):
    rars_path = f"{progs_roots}/rars1_6.jar"
    
    if prog.endswith(".s"):
        asm_file = f"{progs_roots}/{prog}"
        prog_no_ext = prog[:-2]
    elif prog.endswith(".asm"):
        asm_file = f"{progs_roots}/{prog}"
        prog_no_ext = prog[:-4]
    else:
        asm_file = f"{progs_roots}/{prog}.s"
        prog_no_ext = prog
        
    mem_cfg = "mc CompactDataAtZero"
    dump_text = f"dump .text HexText {progs_roots}/{prog_no_ext}_prog.txt"
    dump_data = f"dump .data HexText {progs_roots}/{prog_no_ext}_data.txt"
    regs = "x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31"
    
    print(f"Simulating prog {prog_no_ext} on RARS.")
    rars_cmd = f"java -jar {rars_path} {mem_cfg} {dump_text} {dump_data} {regs} nc {asm_file}"
    
    regs_file = f"{progs_roots}/{prog_no_ext}_regs.txt"
    os.system(f"{rars_cmd} > {regs_file}")
    
    process_rars_output(regs_file)

def get_asm_progs(files_path):
    asm_progs = []
    # for root, _, files in os.walk(files_path):
    for _, _, files in os.walk(files_path):
        for file_name in files:
            if file_name.endswith('.s'):
                # file_name = file_name[:-2]
                asm_progs.append(file_name)
                # asm_progs.append(os.path.join(root, file_name))
            elif file_name.endswith('.asm'):
                # file_name = file_name[:-4]
                asm_progs.append(file_name)
                # asm_progs.append(os.path.join(root, file_name))
    return asm_progs

def process_rars_output(file):
    with open(file, "r") as f:
        lines = f.readlines()
    
    out_str = ""
    for line in lines:
        if len(line.split()) == 2:
            reg_val = line.split()[1][2:]
            out_str += f"{reg_val}\n"
            # print(reg_val)
    
    with open(file, "w") as f:
        f.write(out_str)

def main():
    progs_roots = "../basic_tb/programs"
    prog = "OP"
    if len(argv) > 1:
        assert (len(argv) < 4), "Too many arguments. Use python3 run_rars.py prog_dir prog_name"
        prog = argv[2]
        if len(argv) == 3:
            progs_roots = argv[1]
    
    if prog == "all":
        asm_progs = get_asm_progs(progs_roots)
        # for i in asm_progs: print(i)
        for x in asm_progs:
            run_rars(progs_roots, x)
    else:
        run_rars(progs_roots, prog)

if __name__ == "__main__":
    main()