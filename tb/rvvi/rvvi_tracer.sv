module rvvi_tracer (
    input  logic clk_i,
    input  logic rst_n_i,
    rvviTrace rvvi
);

import core_pkg::*;
// import tb_pkg::*;

`include "riscv_decoder.sv"

bit print_trace;
bit dlyd_rst;

string trace_file;
int cycles;
int trace_fd;

wire [31:0] pc = rvvi.pc_rdata[0][0];
wire [31:0] instr = rvvi.insn[0][0];
wire        trap = rvvi.trap[0][0];

logic [31:0] rd_wdata;
string       rd_str, rd_mnemonic;

csr_addr_t   csr_addr;
logic [31:0] csr_wdata;
string       csr_name, csr_str;

riscv_decoder dec = new();
string mnemonic;
string trace_str;

// cycle counter
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) cycles <= '0;
    else cycles <= cycles + 32'b1;
end

initial begin
    if ($value$plusargs("print_trace=%b", print_trace)) begin
        $display("Got print_trace from plusargs:\n  %b", print_trace);
    end
    trace_file = "trace_core.log";
    // $sformat(info_tag, "CORE_TRACER %2d", hart_id_i);
    // $display("[%s] Output filename is: %s", info_tag, trace_file);
    $display("%t: Output filename is: %s", $time, trace_file);
    trace_fd = $fopen(trace_file, "w");
    
    // $fwrite(f,"        Time |    Cycle | PC       | Assembly                  | Instr    | GPR write     | CSR write        \n");
    // $fwrite(f,"-------------------------------------------------------------------------------------------------------------\n");
    $fdisplay(trace_fd, get_header());
end

always @ (negedge clk_i) begin 
    if (rvvi.valid[0][0]) begin
        mnemonic = dec.decode_instruction (instr);
        
        rd_wdata = '0;
        rd_str = " ";
        foreach(rvvi.x_wb[0][0][i]) begin
            if (rvvi.x_wb[0][0][i]) begin
                rd_mnemonic = dec.translate_register(i);
                rd_wdata = rvvi.x_wdata[0][0][i];
                rd_str = $sformatf("%4s: %h", rd_mnemonic, rd_wdata);
            end;
        end
        
        csr_addr = csr_addr.first();
        csr_str = " ";
        do begin
            if (rvvi.csr_wb[0][0][csr_addr]) begin
                csr_wdata = rvvi.csr[0][0][csr_addr];
                csr_name  = dec.translate_csr (csr_addr);
                csr_str = $sformatf("%s: %h", csr_name, csr_wdata);
            end
            csr_addr = csr_addr.next();
        end while (csr_addr != csr_addr.first());
        
        
        // trace_str = $sformatf("%t | %9d | %h | %-25s | %h | %-14s | %-20s | %b\n", 
        //                       $time, cycles, pc, mnemonic, instr, rd_str, csr_str, trap);
        trace_str = $sformatf("%9d | %h | %-26s | %h | %-14s | %-20s | %b\n", 
                              cycles, pc, mnemonic, instr, rd_str, csr_str, trap);
        
        $fwrite(trace_fd, trace_str);
        if (print_trace) begin
            if (!dlyd_rst) begin
                $display(get_header());
                dlyd_rst = 1;
            end
            $write(trace_str);
        end
    end
end

always @(negedge rst_n_i) dlyd_rst = 0;

function string get_header();
    // get_header = {"        Time |     Cycle | PC       | Assembly                  | Instr    | GPR write      | CSR write        \n",
    //               "---------------------------------------------------------------------------------------------------------------"};
    get_header = {"    Cycle | PC       | Assembly                   | Instr    |   GPR write    | CSR write            | Trap\n",
                  "-----------------------------------------------------------------------------------------------------------"};
endfunction
    

endmodule