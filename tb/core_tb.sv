/* 
    This is the testbench.

    Instruction set: RV32I.
*/

module core_tb;

import core_pkg::*;

localparam int INSTR_MEM_SIZE = 2**12;
localparam int IMEM_AWIDTH = $clog2(INSTR_MEM_SIZE);
localparam int DATA_MEM_SIZE = 2**12;
localparam int DMEM_AWIDTH = $clog2(DATA_MEM_SIZE);

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

//==============   Module instantiations - BEGIN   ==============//

core core_inst (
    .clk_i   ( clk ),
    .rst_n_i ( rst_n ),
    
    .dmem_rdata_i ( dmem_rdata ),
    .dmem_wdata_o ( dmem_wdata ),
    .dmem_addr_o  ( dmem_addr ),
    .dmem_wen_o   ( dmem_wen ),
    .dmem_ben_o   ( dmem_ben ),
    
    .imem_rdata_i ( imem_rdata ),
    .imem_addr_o  ( imem_addr )
);

data_mem #(
    .AWIDTH(DMEM_AWIDTH),
    .DWIDTH(32)
) data_mem_inst (
    .rdata(dmem_rdata),
    .wdata(dmem_wdata),
    .addr(dmem_addr[DMEM_AWIDTH-1:0]),
    .wen(dmem_wen),
    .clk,
    .rst_n,
    .wdata_mask(dmem_ben)
);

rom_mem #(
    .AWIDTH(IMEM_AWIDTH),
    .DWIDTH(32)
) instr_mem (
    .rst_n,
    .rdata(imem_rdata),
    .addr(imem_addr[IMEM_AWIDTH-1:0])
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
int cnt_x_instr;
bit verbose = 0;
logic [31:0] expected;

logic [31:0] regs_clone [32];
assign regs_clone = core_inst.id_stage_inst.register_file_inst.mem;
logic [31:0] dmem_clone [DATA_MEM_SIZE/4];
always_comb foreach(dmem_clone[i]) dmem_clone[i] = data_mem_inst.mem[i*4+:4];
// instr_t instr_clone;
logic [31:0] instr_clone;
assign instr_clone = core_inst.id_stage_inst.instr_id;

logic [31:0] xptd_dmem [DATA_MEM_SIZE/4];
logic [31:0] xptd_regs [32];

string progs [] = '{"OP", "OP-IMM", "LUI_AUIPC", "ST_LD", 
                    "BRANCH", "JAL", "WR_ALL_MEM"};
// The tests below were copied from https://github.com/shrubbroom/Simple-RISC-V-testbench/tree/main
string progs_with_regs [] = '{"1_basic", 
                              "2_hazard_control_0", "2_hazard_data_0", "2_hazard_data_1", 
                              "3_bubble_sort", "3_fib", "3_qsort"};

string prog_name = "3_qsort";
bit check_regs = 1;

localparam int PERIOD = 2;
localparam int MAX_CYCLES = 1000000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    $display ("\n%t: Simulation reached the time limit. Terminating simulation.\n", $time);
    $finish;
end

initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 5); // e.g.: "900ns"

    $display("#==========================================================#");

    // $display("%t: Running program %s.", $time, prog_name);
    
    reset ();
    
    drive_prog(prog_name, check_regs);
    
    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

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

task load_instr_mem (string prog_name, string prog_file);
    logic [31:0] mem [INSTR_MEM_SIZE];
    $readmemh(prog_file, mem);
    foreach(mem[i]) instr_mem.mem[i*4+:4] = mem[i];
endtask

task print_instr_mem;
    for(int i = 0; instr_mem.mem[i*4+:4] != '0; i++) begin
        $display("%t: Read 0x%h from memory address %0d.", $time, instr_mem.mem[i*4+:4], i);
    end
endtask

task print_regs;
    foreach(regs_clone[i]) begin
        $display("%t: Read 0x%h from register %0d.", $time, regs_clone[i], i);
    end
endtask

task load_xptd_dmem (string dmem_file);
    // logic [31:0] mem [INSTR_MEM_SIZE];
    // $readmemh(dmem_file, mem);
    // foreach(mem[i]) xptd_dmem[i] = mem[i];
    $readmemh(dmem_file, xptd_dmem);
endtask
task load_xptd_regs (string regs_file);
    $readmemh(regs_file, xptd_regs);
endtask

task checkit (string what_mem, logic [31:0] expected [], logic [31:0] actual []);
    $display("%t: Checking %s...", $time, what_mem);
    foreach (expected[i]) begin
        if (expected[i] != actual[i]) begin
            n_mismatches++;
            $display("%t: ERROR! Index = %0d. Expected = %h. Actual = %h. Mem = %s.", $time, i, expected[i], actual[i], what_mem);
        end
    end
    $display("%t: Done checking.", $time);
endtask

task drive_prog (string prog_name, bit check_regs);
    string prog_file;
    string dmem_file;
    string regs_file;
    
    if (prog_name != "all") begin
        prog_file = {"programs/", prog_name, "_prog.txt"};
        dmem_file = {"programs/", prog_name, "_data.txt"};
        regs_file = {"programs/", prog_name, "_regs.txt"};
        
        $display("#==========================================================#");
        $display("%t: Executing program %s.", $time, prog_name);
        reset ();
        
        // Load instructions into instruction memory
        load_instr_mem(prog_name, prog_file);
        
        // Wait for instructions to end
        do begin
            @(negedge clk);
            if (instr_clone === 'x) // After the end of instr mem code, there's only unknowns
                cnt_x_instr++;
            else
                cnt_x_instr = 0;
        end while (cnt_x_instr != 4); // Proceed when 4 consecutive 'x instrs happen in ID stage

        // Get expected data memory values (got from RARS simulator)
        load_xptd_dmem(dmem_file);
        if (check_regs)
            load_xptd_regs(regs_file);
        
        if (verbose) begin
            foreach (xptd_dmem[i]) begin
                if(i == 32) break;
                $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
            end
        end
        checkit("dmem", xptd_dmem, dmem_clone);
        
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
        
            drive_prog (single_prog, 0);
        end
    end
endtask

//==============   Tasks and functions - END   ==============//

endmodule