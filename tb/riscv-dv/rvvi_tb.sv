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

// localparam int TEXT_START_ADDR = 32'h0000_3000;
// localparam int TEXT_END_ADDR   = 32'h0000_3ffc;
// localparam int TEXT_SIZE       = TEXT_END_ADDR - TEXT_START_ADDR;
int section_text_start = 32'h0000_3000;
int section_text_end   = 32'h0000_3ffc;
int section_text_size  = section_text_end - section_text_start;

logic [31:0] instr_mem [];
logic [31:0] instr_addr, idx;
assign instr_addr = imem_addr - section_text_start;
bit fetch_enable = 0;
bit prog_end;
always_comb begin
    imem_rdata = '0;
    // instr_addr = (imem_addr >= section_text_start) ? (imem_addr - section_text_start) : ('0);
    if (fetch_enable) begin
        idx = instr_addr >> 2;
        if (idx > instr_mem.size() && !prog_end) begin
            $display("%t: Out of bounds access to instr mem. Terminating...", $time);
            $display("%t: Allowed range: %h - %h.", $time, section_text_start, section_text_end);
            // $display("%t: Accessed addr: %h.", $time, instr_addr);
            $display("%t: Accessed addr: %h.", $time, imem_addr);
            $finish;
        end
        else begin
            imem_rdata = instr_mem[idx];
        end
    end
end
// assign imem_rdata = instr_mem[instr_addr];
// always_ff @(negedge clk or negedge rst_n) begin
//     if (!rst_n) begin
//         imem_rdata <= '0;
//     end
//     begin
//         imem_rdata <= '0;
//         // instr_addr = (imem_addr >= section_text_start) ? (imem_addr - section_text_start) : ('0);
//         if (fetch_enable) begin
//             if (instr_addr/4 < instr_mem.size()) begin
//                 imem_rdata = instr_mem[instr_addr];
//                 if ($time < 20)
//                 $display("%t: Drove instr: %h.", $time, imem_rdata);
//             end
//             else begin
//                 $display("%t: Out of bounds access to instr mem.", $time);
//                 $display("%t: Allowed range: %h - %h.", $time, section_text_start, section_text_end);
//                 $display("%t: Accessed addr: %h.", $time, instr_addr);
//                 $display("%t: Accessed addr/4: %h.", $time, instr_addr/4);
//                 $display("%t: Accessed imem_addr: %h.", $time, imem_addr);
//                 $display("%t: Accessed section_text_start: %h.", $time, section_text_start);
//                 $finish;
//             end
//         end
//     end
// end


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
    .NHART(1),   // Number of harts reported
    .RETIRE(1)    // Number of instructions that can retire during valid event
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
    .rdata_a (dmem_rdata),
    .wdata_a (dmem_wdata),
    .addr_a  (dmem_addr[ADDR_WIDTH-1:0]),
    .wen_a   (dmem_wen),
    .ben_a   (dmem_ben),
    
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
int file, status;

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

string progs [] = '{"OP", "OP-IMM", "LUI_AUIPC", "ST_LD", //
                    "BRANCH", "JAL", "WR_ALL_MEM", //};
// The tests below were copied from https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main
                    "1_basic", 
                    "2_hazard_control_0", "2_hazard_data_0", "2_hazard_data_1", 
                    "3_bubble_sort", "3_fib", "3_qsort"};
// string progs_with_regs [] = '{"1_basic", 
//                               "2_hazard_control_0", "2_hazard_data_0", "2_hazard_data_1", 
//                               "3_bubble_sort", "3_fib", "3_qsort"};

string prog_name = "LUI_AUIPC";
string progs_path = "../basic_tb/programs";
bit check_regs = 1, check_mem = 1;

localparam int PERIOD = 2;
localparam int MAX_CYCLES = 1000000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    $display ("\n%t: Simulation reached the time limit. Terminating simulation.\n", $time);
    $finish;
end

always @(posedge clk) cycle_cnt++;

initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 12); // e.g.: "900ns"

    $display("#==========================================================#");
    
    fetch_enable = 0;
    reset ();
    
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
        
    drive_prog(prog_name, check_regs, check_mem);
    
    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);
    $display("%t: Clock cycles: %0d.", $time, cycle_cnt);

    $display("#==========================================================#");
    $finish;
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
    // logic [31:0] mem [TEXT_SIZE];
    logic [31:0] mem [];
    int addr;
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
    section_text_size = num_entries*4;
    // section_text_size = num_entries;
    section_text_end = section_text_start + section_text_size;
    if(verbose) begin
        $display("%t: section_text_size in words = %h.", $time, num_entries);
        $display("%t: section_text_size in bytes = %h.", $time, section_text_size);
        $display("%t: Section .text range = [%h, %h].", $time, section_text_start, section_text_end);
    end
    
    mem = new [num_entries];
    instr_mem = new [num_entries];
    
    
    foreach(mem[i]) mem[i] = '0;
    $readmemh(prog_file, mem);
    foreach(mem[i]) begin
        // $display("%t: mem[%d] %h.", $time, i, mem[i]);
        // addr = i*4 + section_text_start;
        if (mem[i] !== 'x) begin
            // addr = i*4 + section_text_start;
            // mem_inst.mem[addr  ] = mem[i][ 0+:8];
            // mem_inst.mem[addr+1] = mem[i][ 8+:8];
            // mem_inst.mem[addr+2] = mem[i][16+:8];
            // mem_inst.mem[addr+3] = mem[i][24+:8];
            
            instr_mem[i] = mem[i];
        end
    end
    // print_instr_mem();
endtask

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
        
        // do begin
        //     @(negedge clk);
        //     // if (instr_clone === 'x) // After the end of instr mem code, there's only unknowns
        //     if (imem_rdata === '0) // After the end of instr mem code, there's only zeros
        //         cnt_x_instr++;
        //     else
        //         cnt_x_instr = 0;
        //     // $display("%t: Instr in WB stage is = %h. %g", $time, wrapper_inst.rvfi_insn, rvvi.valid[0][0]);
        // end while (cnt_x_instr != 6); // Proceed when IF stage has 6 consecutive blank instr
        
        // An ecall marks the end of the program
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
                    $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
                end
            end
            checkit("dmem", xptd_dmem, dmem_clone);
        end
        
        if (check_regs) begin
            if (verbose)
                foreach (xptd_regs[i])
                    $display("xptd_regs[%2d] = %h. reg[%2d] = %h.", i, xptd_regs[i], i, regs_clone[i]);
            checkit("regs", xptd_regs, regs_clone);
        end

        $display("%t: Finished executing program %s.", $time, prog_name);
        $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);
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

//==============   Tasks and functions - END   ==============//

endmodule