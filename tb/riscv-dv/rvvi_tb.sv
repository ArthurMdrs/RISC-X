module riscv_dv_tb;

import tb_pkg::*;

localparam ISA_M = 0;
localparam ISA_C = 1;
localparam ISA_F = 0;

// Primary inputs
logic clk;
logic rst_n;

// Data memory interface
logic [31:0] dmem_rdata;
logic [31:0] dmem_wdata;
logic [31:0] dmem_addr;
logic        dmem_wen;
logic  [3:0] dmem_ben;

// Instruction memory interface
logic [31:0] imem_rdata;
logic [31:0] imem_addr;

// The start of .text will be the core's first fetch
int section_text_start = 32'h0000_3000;

// Data memory will be an associative array
logic [31:0] data_mem [logic [31:0]];

wire [31:0] hartid    = 32'h0000_0000;
wire [23:0] mtvec     = 24'h8000_80;
wire [29:0] boot_addr = section_text_start[31:2];

`define CORE wrapper_inst.core_inst

//==============   Module instantiations - BEGIN   ==============//

rvviTrace #(
    .ILEN(32),  // Instruction length in bits
    .XLEN(32),  // GPR length in bits
    .FLEN(32),  // FPR length in bits
    .VLEN(256), // Vector register size in bits
    .NHART(1),  // Number of harts reported
    .RETIRE(1)  // Number of instructions that can retire during valid event
) rvvi ();

rvvi_wrapper #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) wrapper_inst (
    .clk_i   ( clk ),
    .rst_n_i ( rst_n ),
    
    .dmem_rdata_i ( dmem_rdata ),
    .dmem_wdata_o ( dmem_wdata ),
    .dmem_addr_o  ( dmem_addr ),
    .dmem_wen_o   ( dmem_wen ),
    .dmem_ben_o   ( dmem_ben ),
    
    .imem_rdata_i ( imem_rdata ),
    .imem_addr_o  ( imem_addr ),
    
    .hartid_i    ( hartid ),
    .mtvec_i     ( mtvec ),
    .boot_addr_i ( boot_addr ),
    
    .rvvi ( rvvi )
);

rvvi_tracer tracer_inst (
    .clk_i   ( clk ),
    .rst_n_i ( rst_n ),
    .rvvi ( rvvi )
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches, cycle_cnt;
bit verbose = 0;
bit check_regs = 1, check_mem = 1;
bit fetch_enable;

section_info_t sections[$]; // Dynamic array of section information

logic [31:0] regs_clone [32];
assign regs_clone[1:31] = `CORE.id_stage_inst.register_file_inst.mem;
assign regs_clone[0] = '0;

logic [31:0] xptd_dmem [1024];
logic [31:0] xptd_regs [32];

// The array below contains simple assembly programs found in $(TB_HOME)/../programs
string progs [] = '{"OP", "OP-IMM", "LUI_AUIPC", "ST_LD",
                    "BRANCH", "JAL", "WR_ALL_MEM",
// The tests below were copied from https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main
                    "1_basic", 
                    "2_hazard_control_0", "2_hazard_data_0", "2_hazard_data_1", 
                    "3_bubble_sort", "3_fib", "3_qsort"};

string prog_name = "LUI_AUIPC";
string progs_path = "../programs";
string bin_file = {"/mytest/asm_test/", prog_name, ".bin"};
string sections_file = {"/mytest/asm_test/", prog_name, ".section"};

// Generate clock
localparam int PERIOD = 2;
localparam int MAX_CYCLES = 100000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    $display ("\n%t: Simulation reached the time limit. Terminating simulation.\n", $time);
    $finish;
end

// Cycle counter (not the same as tracer_inst.cycles)
always @(posedge clk) cycle_cnt++;

initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 12); // e.g.: "       900ns"

    $display("#==========================================================#");
    
    if ($value$plusargs("prog=%s", prog_name)) begin
        $display("Got prog from plusargs:\n  %s.", prog_name);
    end
    if ($value$plusargs("progs_path=%s", progs_path)) begin
        $display("Got progs_path from plusargs:\n  %s", progs_path);
    end
    if ($value$plusargs("check_regs=%b", check_regs)) begin
        $display("Got check_regs from plusargs:\n  %b", check_regs);
    end
    if ($value$plusargs("check_mem=%b", check_mem)) begin
        $display("Got check_mem from plusargs:\n  %b", check_mem);
    end
    if ($value$plusargs("text_start=%h", section_text_start)) begin
        $display("Got text_start from plusargs:\n  %h", section_text_start);
    end
    if ($value$plusargs("verbose=%b", verbose)) begin
        $display("Got verbose from plusargs:\n  %b", verbose);
    end
    if ($value$plusargs("bin=%s", bin_file)) begin
        $display("Got bin_file from plusargs:\n  %s.", bin_file);
    end
    if ($value$plusargs("section=%s", sections_file)) begin
        $display("Got sections_file from plusargs:\n  %s.", sections_file);
    end
    
    fetch_enable = 0;
    reset ();
        
    drive_prog(prog_name, check_regs, check_mem);
    
    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);
    $display("%t: Clock cycles: %0d.", $time, cycle_cnt);
    
    // print_data_mem();

    $display("#==========================================================#");
    $finish;
end

// Check if instruction memory access is valid
always_comb begin
    if (fetch_enable) begin
        if (imem_addr[0] == 1'b0) begin
            data_mem_load (imem_addr, 4'b1111, imem_rdata);
        end
        else begin
            $display("%t: Misaligned instruction address! Accessed addr: %h.", $time, imem_addr);
            $finish;
        end
    end
end

// Perform writes and reads to/from memory
always @(negedge clk, negedge rst_n) begin
    if (!rst_n) begin
        data_mem.delete();
    end else begin
        if (dmem_wen)
            data_mem_store (dmem_addr, dmem_ben, dmem_wdata);
        data_mem_load (dmem_addr, dmem_ben, dmem_rdata);
    end
end

//=================   Simulation - END   =================//

//==============   Tasks and functions - BEGIN   ==============//

task reset ();
    @(negedge clk);
    rst_n = 0;
    @(negedge clk);
    rst_n = 1;
    $display("%t: Reset done.", $time);
endtask

function automatic void data_mem_store (logic [31:0] addr, logic [3:0] ben, logic [31:0] wdata);
    logic [31:0] addr_int, wdata_int;
    addr_int = {addr[31:2], 2'b0}; // We can only access 4-byte aligned addresses
    wdata_int = '0;
    if (data_mem.exists(addr_int)) wdata_int = data_mem[addr_int];
    case (addr[1:0])
        2'b00: begin
            if(ben[0]) wdata_int[ 7: 0] = wdata[ 7: 0];
            if(ben[1]) wdata_int[15: 8] = wdata[15: 8];
            if(ben[2]) wdata_int[23:16] = wdata[23:16];
            if(ben[3]) wdata_int[31:24] = wdata[31:24];
            data_mem[addr_int] = wdata_int;
        end
        2'b01: begin
            if(ben[0]) wdata_int[15: 8] = wdata[ 7: 0];
            if(ben[1]) wdata_int[23:16] = wdata[15: 8];
            if(ben[2]) wdata_int[31:24] = wdata[23:16];
            data_mem[addr_int] = wdata_int;
            if(ben[3]) begin
                addr_int += 32'd4;
                data_mem_store (addr_int, 4'b0001, {24'b0, wdata[31:24]});
            end
        end
        2'b10: begin
            if(ben[0]) wdata_int[23:16] = wdata[ 7: 0];
            if(ben[1]) wdata_int[31:24] = wdata[15: 8];
            data_mem[addr_int] = wdata_int;
            if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_store (addr_int, 4'b0011, {16'b0, wdata[31:16]});
            end
        end
        2'b11: begin
            if(ben[0]) wdata_int[31:24] = wdata[ 7: 0];
            data_mem[addr_int] = wdata_int;
            if(ben[3:1] == 3'b001) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_store (addr_int, 4'b0001, {24'b0, wdata[15:8]});
            end
            else if(ben[3:1] == 3'b111) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_store (addr_int, 4'b0111, {8'b0, wdata[31:8]});
            end
        end
    endcase
endfunction

function automatic void data_mem_load (logic [31:0] addr, logic [3:0] ben, output logic [31:0] rdata);
    logic [31:0] addr_int, rdata_int, rdata_aux;
    addr_int = {addr[31:2], 2'b0}; // We can only access 4-byte aligned addresses
    rdata_int = '0;
    if (data_mem.exists(addr_int)) rdata_int = data_mem[addr_int];
    case (addr[1:0])
        2'b00: begin
            // if(ben[0]) rdata_int[ 7: 0] = wdata[ 7: 0];
            // if(ben[1]) rdata_int[15: 8] = wdata[15: 8];
            // if(ben[2]) rdata_int[23:16] = wdata[23:16];
            // if(ben[3]) rdata_int[31:24] = wdata[31:24];
            rdata = rdata_int;
        end
        2'b01: begin
            rdata_int = rdata_int >> 8;
            rdata = rdata_int;
            if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_load (addr_int, 4'b0001, rdata_aux);
                rdata[31:24] = rdata_aux[7:0];
            end
        end
        2'b10: begin
            rdata_int = rdata_int >> 16;
            rdata = rdata_int;
            if(ben[3:2] == 2'b11) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_load (addr_int, 4'b0011, rdata_aux);
                rdata[31:16] = rdata_aux[15:0];
            end
        end
        2'b11: begin
            rdata_int = rdata_int >> 24;
            rdata = rdata_int;
            if(ben[3:1] == 3'b001) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_load (addr_int, 4'b0001, rdata_aux);
                rdata[15:8] = rdata_aux[7:0];
            end
            else if(ben[3:1] == 3'b111) begin // We assume ben is one of: 0001, 0011, 1111
                addr_int += 32'd4;
                data_mem_load (addr_int, 4'b0111, rdata_aux);
                rdata[31:8] = rdata_aux[23:0];
            end
        end
    endcase
endfunction

function void print_data_mem ();
    foreach(data_mem[i])
        $display("%t: data_mem[%h] = 0x%h.", $time, i, data_mem[i]);
endfunction

function void check_data_mem ();
    logic [31:0] addr_sh;
    foreach(xptd_dmem[addr]) begin
        addr_sh = addr << 2;
        if (data_mem.exists(addr_sh)) begin
            if (data_mem[addr_sh] != xptd_dmem[addr]) begin
                n_mismatches++;
                $display("%t: ERROR in data mem! Index = %0d. Expected = %h. Actual = %h.", $time, addr, xptd_dmem[addr], data_mem[addr_sh]);
            end
        end
        else begin
            if (xptd_dmem[addr] != '0) begin
                n_mismatches++;
                $display("%t: ERROR in data mem! Index = %0d. Expected = %h. Actual = %h (does not exist).", $time, addr, xptd_dmem[addr], data_mem[addr_sh]);
            end
        end
    end
endfunction

task print_regs;
    foreach(regs_clone[i]) begin
        $display("%t: Read 0x%h from register %0d.", $time, regs_clone[i], i);
    end
endtask

task load_xptd_dmem (string dmem_file);
    $readmemh(dmem_file, xptd_dmem);
endtask
task load_xptd_regs (string regs_file);
    $readmemh(regs_file, xptd_regs);
endtask

task checkit (string what_mem, logic [31:0] expected [], logic [31:0] actual []);
    $display("%t: Checking %s...", $time, what_mem);
    assert(expected.size() == actual.size()) else $display("Sizes don't match!");
    foreach (expected[i]) begin
        if (expected[i] != actual[i]) begin
            n_mismatches++;
            $display("%t: ERROR! Index = %0d. Expected = %h. Actual = %h. Mem = %s.", $time, i, expected[i], actual[i], what_mem);
        end
    end
    $display("%t: Done checking.", $time);
endtask

task drive_prog (string prog_name, bit check_regs, bit check_mem);
    // string prog_file;
    string dmem_file;
    string regs_file;
    
    if (prog_name != "all") begin
        // prog_file = {progs_path, "/", prog_name, "_prog.txt"};
        dmem_file = {progs_path, "/", prog_name, "_data.txt"};
        regs_file = {progs_path, "/", prog_name, "_regs.txt"};
        
        $display("#==========================================================#");
        $display("%t: Executing program %s.", $time, prog_name);
        reset ();
        fetch_enable = 1;
        // prog_end = 0;
    
        read_sections(sections_file);
        if (verbose) begin
            $display("Section info: Start Addr   End Addr   Size   Alignment");
            foreach (sections[i])
                $display("Section %s: 0x%h, 0x%h, 0x%h, 2**%0d", sections[i].name, sections[i].start_addr, sections[i].end_addr, sections[i].size, sections[i].alignment);
        end
    
        load_memory(bin_file, sections);
        
        // print_section(".text");
        
        // Load instructions into instruction memory
        // load_instr_mem(prog_file);
        
        // Wait for instructions to end
        // An ecall marks the end of the program (RISCV-DV convention)
        while (rvvi.insn[0][0] != 32'h00000073) begin// ecall
            @(negedge clk);
            // if (imem_rdata == 32'h00000073)
            //     prog_end = 1;
        end
        @(negedge clk);
        fetch_enable = 0;

        // Get expected data memory values (got from RARS simulator)
        if (check_mem)
            load_xptd_dmem(dmem_file);
        if (check_regs)
            load_xptd_regs(regs_file);
        
        if (check_mem) begin
            if (verbose) begin
                foreach (xptd_dmem[i]) begin
                    if(i == 32) break;
                    // $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
                    $display("xptd_dmem[%2d] = %h. data_mem[%2d] = %h.", i, xptd_dmem[i], i, data_mem[i<<2]);
                end
            end
            // checkit("dmem", xptd_dmem, dmem_clone);
            check_data_mem ();
        end
        
        if (check_regs) begin
            // if (verbose)
            //     foreach (xptd_regs[i])
            //         $display("xptd_regs[%2d] = %h. reg[%2d] = %h.", i, xptd_regs[i], i, regs_clone[i]);
            checkit("regs", xptd_regs, regs_clone);
        end

        $display("%t: Finished executing program %s.", $time, prog_name);
        $display("%t: Clock cycles: %0d.", $time, tracer_inst.cycles);
        $display("%t: Number of mismatches: %0d.", $time, n_mismatches);
        $display("#==========================================================#");
    end // if (prog_name != "all")
    else begin
        foreach(progs[i]) begin
            string single_prog;
            single_prog = progs[i];
        
            drive_prog (single_prog, 1, 1);
        end
    end
endtask

// function to read sections file and populate sections array
function void read_sections (string sections_file);
    string line;
    string name;
    logic [31:0] start_addr, end_addr, size;
    int alignment;
    int fd, code;
    section_info_t section;

    // Open the file
    fd = $fopen(sections_file, "r");
    if (fd == 0) begin
        $fatal(1, "Failed to open %s.", sections_file);
    end

    // Skip the first line (header)
    code = $fgets(line, fd);

    // Read the rest of the lines
    while (!$feof(fd)) begin
        // Read section name
        code = $fscanf(fd, "%s\n", name);
        if(code == -1) begin
            break;
        end
        
        // Read line with infos
        code = $fgets(line, fd);
        code = $sscanf(line, "%x,%x,%x,%d\n", start_addr, end_addr, size, alignment);

        // Add the section information to the array
        if (code == 4) begin
            section.name = name;
            section.start_addr = start_addr;
            section.end_addr = end_addr;
            section.size = size;
            section.alignment = alignment;
            sections.push_back(section);
        end else begin
            $fatal(1, "Wrong number of data items.");
        end
    end

    // Close the file
    $fclose(fd);
endfunction

// function to load .bin into the memory
function void load_memory (string bin_file, section_info_t sections[$]);
    int fd;
    logic [31:0] addr, word;
    // int i, n;
    int n;
    logic [31:0] align_mask;

    // Open .bin file
    fd = $fopen(bin_file, "r");
    if (fd == 0) begin
        $fatal(1, "Failed to open %s.", bin_file);
    end

    // $display("Number of sections = %0d.", sections.size());
    
    // Load data into memory according to the sections information
    // We assume that sections[0] is the first section (lowest start address)
    addr = sections[0].start_addr;
    foreach (sections[i]) begin
        // $display("Addr at start of %s. Addr = 0x%h.", sections[i].name, addr);
        
        align_mask = (32'b1 << sections[i].alignment) - 1;
        // $display("align_mask = %h.", align_mask);
        
        if (addr & align_mask != '0) begin
            $display("addr && align_mask = 0x%h.", addr && align_mask);
            $display("Found misalignment for section %s. Addr = 0x%h, alignment = %0d.", sections[i].name, sections[i].start_addr, sections[i].alignment);
        end
        
        while (addr <= sections[i].end_addr) begin
            n = $fread(word, fd);
            if (n != 4) begin
                $fatal(1, "Error reading .bin at address 0x%h.", addr);
            end
            
            if (sections[i].name.substr(0,7) == ".region_") begin
                // Account for endianess
                word = {word[7:0], word[15:8], word[23:16], word[31:24]};
                data_mem[addr] = word;
            end 
            if (sections[i].name == ".text") begin
                // Account for endianess
                word = {word[7:0], word[15:8], word[23:16], word[31:24]};
                data_mem[addr] = word;
            end 
            
            addr += 4;
        end
    end

    // Close the file
    $fclose(fd);
endfunction

function void print_section (string section, int stop = 100);
    int k;
    foreach (sections[i]) begin
        if (sections[i].name == section) begin
            $display("%t: Printing section %s of size 0x%h.", $time, section, sections[i].size);
            k = 0;
            for (int j = sections[i].start_addr; j <= sections[i].end_addr; j += 4) begin
                if (k == stop) break;
                $display("%s[0x%h] = 0x%h", section, j, data_mem[j]);
                k++;
            end
            return;
        end
    end
endfunction

//==============   Tasks and functions - END   ==============//

endmodule