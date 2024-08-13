module riscv_dv_tb;

localparam int ADDR_WIDTH = 16;
localparam int MEM_SIZE = 2**ADDR_WIDTH;

localparam ISA_M = 0;
localparam ISA_C = 0;
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

// Define instruction memory bounds
int section_text_start = 32'h0000_3000;
int section_text_end   = 32'h0000_3ffc;
int section_text_size  = section_text_end - section_text_start;

// Instruction memory will be a dynamic array
logic [31:0] instr_mem [];
// Translate real memory address to array index
logic [31:0] instr_addr, imem_idx;
assign instr_addr = imem_addr - section_text_start;
assign imem_idx = instr_addr >> 2; // The array is word-addressable, so this shift is needed

// Data memory will be an associative array
logic [31:0] data_mem [logic [31:0]];
logic [31:0] region_0 [logic [31:0]];
logic [31:0] dmem_rdata_aux;

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

mem #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(32)
) mem_inst (
    .clk,
    .rst_n,
    
    // Port a (data)
    // .rdata_a (dmem_rdata),
    // .wdata_a (dmem_wdata),
    // .addr_a  (dmem_addr[ADDR_WIDTH-1:0]),
    // .wen_a   (dmem_wen),
    // .ben_a   (dmem_ben),
    
    .rdata_a (),
    .wdata_a ('0),
    .addr_a  ('0),
    .wen_a   ('0),
    .ben_a   ('0),
    
    // Port b (instruction)
    // .rdata_b (imem_rdata),
    .rdata_b (),
    .wdata_b (32'b0),
    // .addr_b  (imem_addr[ADDR_WIDTH-1:0]),
    .addr_b  ('0),
    .wen_b   (1'b0),
    .ben_b   (4'b0)
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches, cycle_cnt;
int cnt_x_instr;
bit verbose = 0;
bit check_regs = 1, check_mem = 1;
int file, status;
bit fetch_enable;
bit prog_end;

typedef struct {
    string       name;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
    logic [31:0] size;
    int          alignment;
} section_info_t;

section_info_t sections[$]; // Dynamic array of section information

logic [31:0] regs_clone [32];
assign regs_clone[1:31] = `CORE.id_stage_inst.register_file_inst.mem;
assign regs_clone[0] = '0;
logic [31:0] dmem_clone [MEM_SIZE/4];
always_comb 
    foreach(dmem_clone[i]) begin //dmem_clone[i] = mem_inst.mem[i*4+:4];
        dmem_clone[i][ 0+:8] = mem_inst.mem[i*4  ];
        dmem_clone[i][ 8+:8] = mem_inst.mem[i*4+1];
        dmem_clone[i][16+:8] = mem_inst.mem[i*4+2];
        dmem_clone[i][24+:8] = mem_inst.mem[i*4+3];
    end
logic [31:0] instr_clone;
assign instr_clone = `CORE.id_stage_inst.instr_id;

logic [31:0] xptd_dmem [MEM_SIZE/4];
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
localparam int MAX_CYCLES = 1000000;
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
    
    read_sections(sections_file);
    // foreach (sections[i])
    //     $display("Section %s: 0x%h, 0x%h, 0x%h, 2**%0d", sections[i].name, sections[i].start_addr, sections[i].end_addr, sections[i].size, sections[i].alignment);
    
    load_memory(bin_file);
    // $display("Section .region_0 size: 0x%h", region_0.size()*4);
    // foreach (region_0[i])
    //     $display("region_0[0x%h] = 0x%h", i, region_0[i]);
    
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
    imem_rdata = '0;
    if (fetch_enable) begin
        if (imem_idx > instr_mem.size() && !prog_end) begin
            $display("%t: Out of bounds access to instr mem. Terminating...", $time);
            $display("%t: Allowed range: %h - %h.", $time, section_text_start, section_text_end);
            // $display("%t: Accessed addr: %h.", $time, instr_addr);
            $display("%t: Accessed addr: %h.", $time, imem_addr);
            $finish;
        end
        else begin
            imem_rdata = instr_mem[imem_idx];
        end
    end
end

// Update data mem associative array
always @(negedge clk, negedge rst_n) begin
    if (!rst_n) begin
        data_mem.delete();
    end else begin
        if (dmem_wen)
            data_mem_store (dmem_addr, dmem_ben, dmem_wdata);
        data_mem_load (dmem_addr, dmem_ben, dmem_rdata);
        
        // data_mem_load (dmem_addr, dmem_ben, dmem_rdata_aux);
        // if (`CORE.reg_mem_wen_wb || dmem_wen)
        // if (`CORE.reg_mem_wen_mem)
        //     if (dmem_rdata_aux != dmem_rdata) begin
        //         $display("%t: ERROR. Read data_mem[%h] = 0x%h. dmem_rdata = 0x%h.", $time, dmem_addr, dmem_rdata_aux, dmem_rdata);
        //         $display("%t: ERROR. data_mem[%h] = 0x%h.", $time, {dmem_addr[31:2], 2'b0}, data_mem[dmem_addr]);
        //         $display("%t: ERROR. data_mem[%h] = 0x%h.", $time, {dmem_addr[31:2], 2'b0}+32'd4, data_mem[dmem_addr]);
        //     end
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

task load_instr_mem (string prog_file);
    int num_entries;
    string line;
    
    file = $fopen(prog_file, "r");
    if (file == 0) begin
        $display("%t: Error opening file: %s.", $time, prog_file);
        $finish;
    end
    
    // Count the number of entries
    num_entries = 0;
    while (!$feof(file)) begin
      status = $fgets(line, file);
      if (status != 0) begin
        num_entries++;
      end
    end
    
    // Define instruction memory bounds
    section_text_size = num_entries*4;
    section_text_end = section_text_start + section_text_size;
    if(verbose) begin
        $display("%t: section_text_size in words = %h.", $time, num_entries);
        $display("%t: section_text_size in bytes = %h.", $time, section_text_size);
        $display("%t: Section .text range = [%h, %h].", $time, section_text_start, section_text_end);
    end
    
    // Read instruction memory from file
    instr_mem = new [num_entries];
    $readmemh(prog_file, instr_mem);
    
    // print_instr_mem();
endtask

function void data_mem_store (logic [31:0] addr, logic [3:0] ben, logic [31:0] wdata);
    // if (ben[0])
    //     data_mem[addr  ] = wdata[ 7: 0];
    // if (ben[1])
    //     data_mem[addr+1] = wdata[15: 8];
    // if (ben[2])
    //     data_mem[addr+2] = wdata[23:16];
    // if (ben[3])
    //     data_mem[addr+3] = wdata[31:24];
    
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

function void data_mem_load (logic [31:0] addr, logic [3:0] ben, output logic [31:0] rdata);
    // rdata[ 7: 0] = data_mem[addr  ];
    // rdata[15: 8] = data_mem[addr+1];
    // rdata[23:16] = data_mem[addr+2];
    // rdata[31:24] = data_mem[addr+3];
    
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
    logic [31:0] idx, last_idx;
    logic [31:0] data;
    // for (void'(data_mem.first(i)); i != null; void'(data_mem.next(i))) begin
    //     data = {data_mem[i+3], data_mem[i+2], data_mem[i+1], data_mem[i]};
    //     $display("%t: data_mem[%h] = 0x%h.", $time, i, data);
    // end
    
    // if (data_mem.size() != 0) begin
    //     $display("%t: data_mem size = %0d.", $time, data_mem.size()/4);
    //     void'(data_mem.last(last_idx));
    //     void'(data_mem.first(idx));
    //     while (1) begin
    //         // data = data_mem[idx];
    //         data = {data_mem[idx+3], data_mem[idx+2], data_mem[idx+1], data_mem[idx]};
    //         $display("%t: data_mem[%h] = 0x%h.", $time, idx, data);

    //         idx += 3;
    //         if (idx == last_idx)
    //             break;
            
    //         void'(data_mem.next(idx));
    //     end
    // end
    
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

task print_instr_mem;
    logic [31:0] data;
    for(int i = section_text_start; i <= section_text_end; i += 4) begin
        data[ 0+:8] = mem_inst.mem[i  ];
        data[ 8+:8] = mem_inst.mem[i+1];
        data[16+:8] = mem_inst.mem[i+2];
        data[24+:8] = mem_inst.mem[i+3];
        $display("%t: Read 0x%h from memory address %8h.", $time, data, i);
    end
endtask

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
    string prog_file;
    string dmem_file;
    string regs_file;
    
    if (prog_name != "all") begin
        prog_file = {progs_path, "/", prog_name, "_prog.txt"};
        dmem_file = {progs_path, "/", prog_name, "_data.txt"};
        regs_file = {progs_path, "/", prog_name, "_regs.txt"};
        
        $display("#==========================================================#");
        $display("%t: Executing program %s.", $time, prog_name);
        reset ();
        fetch_enable = 1;
        prog_end = 0;
        
        // Load instructions into instruction memory
        load_instr_mem(prog_file);
        
        // Wait for instructions to end
        // An ecall marks the end of the program (RISCV-DV convention)
        while (rvvi.insn[0][0] != 32'h00000073) begin// ecall
            @(negedge clk);
            if (imem_rdata == 32'h00000073)
                prog_end = 1;
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
        if(code == -1)
            break;
        
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
            $fatal(1, "Wrong number of data.");
        end
    end

    // Close the file
    $fclose(fd);
endfunction

// function to load .bin into the memory
function void load_memory (string bin_file);
    int fd;
    logic [31:0] addr, word;
    int i, n;
    logic [31:0] align_mask;

    // Open .bin file
    fd = $fopen(bin_file, "r");
    if (fd == 0) begin
        $fatal(1, "Failed to open %s.", bin_file);
    end

    $display("Number of sections = %0d.", sections.size());
    
    // Load data into memory according to the sections information
    addr = sections[0].start_addr;
    foreach (sections[i]) begin
        $display("Addr at start of %s. Addr = 0x%h.", sections[i].name, addr);
        
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
            
            
            if (sections[i].name == ".region_0") begin
                // Account for endianess
                word = {word[7:0], word[15:8], word[23:16], word[31:24]};
                // memory[addr] = word;
                region_0[addr] = word;
            end 
            
            
            addr += 4;
        end
    end

    // Close the file
    $fclose(fd);
endfunction

//==============   Tasks and functions - END   ==============//

endmodule