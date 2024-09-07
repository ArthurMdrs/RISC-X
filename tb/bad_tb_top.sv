module tb_top;

import uvm_pkg::*;
`include "uvm_macros.svh"

import riscx_pkg::*;

localparam bit ISA_M = 0;
localparam bit ISA_C = 1;
localparam bit ISA_F = 0;

localparam int ILEN = 32;
localparam int XLEN = 32;
localparam int FLEN = 32;

logic clk;
logic rst_n;
logic dlyd_rst_n;

// The start of .text will be the core's first fetch
int fetch_start_addr = 32'h0000_3000;

wire [31:0] hartid    = 32'h0000_0000;
wire [23:0] mtvec     = 24'h8000_80;
wire [29:0] boot_addr = fetch_start_addr[31:2];

assign clk   = if_clknrst.clk;
assign rst_n = if_clknrst.rst_n;

// Interfaces instances - begin
    clknrst_if                  if_clknrst          ();
    bad_uvc_if                  if_instr_bad_uvc    (.clk(clk), .rst_n(rst_n));
    bad_uvc_if                  if_data_bad_uvc     (.clk(clk), .rst_n(rst_n));
    rvvi_if#(ILEN,XLEN,FLEN)    if_rvvi             (.clk(clk), .rst_n(rst_n));
// Interfaces instances - end

//==============   Module instantiations - BEGIN   ==============//

// stub dut(
//     .clk(clk),
//     // .rst_n(rst_n),
//     .rst_n(dlyd_rst_n),

//     .dmem_rdata_i ( if_data_bad_uvc.rdata ),
//     .dmem_wdata_o ( if_data_bad_uvc.wdata ),
//     .dmem_addr_o  ( if_data_bad_uvc.addr ),
//     .dmem_wen_o   ( if_data_bad_uvc.we ),
//     .dmem_ben_o   ( if_data_bad_uvc.be ),
    
//     .imem_rdata_i ( if_instr_bad_uvc.rdata ),
//     .imem_addr_o  ( if_instr_bad_uvc.addr )
// );

// rvviTrace #(
//     .ILEN(32),  // Instruction length in bits
//     .XLEN(32),  // GPR length in bits
//     .FLEN(32),  // FPR length in bits
//     .VLEN(256), // Vector register size in bits
//     .NHART(1),  // Number of harts reported
//     .RETIRE(1)  // Number of instructions that can retire during valid event
// ) rvvi ();

// rvvi_wrapper #(
//     .ISA_M(ISA_M),
//     .ISA_C(ISA_C),
//     .ISA_F(ISA_F)
// ) wrapper_inst (
//     .clk_i   ( clk ),
//     // .rst_n_i ( rst_n ),
//     .rst_n_i ( dlyd_rst_n ),

//     .dmem_rdata_i ( if_data_bad_uvc.rdata ),
//     .dmem_wdata_o ( if_data_bad_uvc.wdata ),
//     .dmem_addr_o  ( if_data_bad_uvc.addr ),
//     .dmem_wen_o   ( if_data_bad_uvc.we ),
//     .dmem_ben_o   ( if_data_bad_uvc.be ),
    
//     .imem_rdata_i ( if_instr_bad_uvc.rdata ),
//     .imem_addr_o  ( if_instr_bad_uvc.addr ),
    
//     .hartid_i    ( hartid ),
//     .mtvec_i     ( mtvec ),
//     .boot_addr_i ( boot_addr ),
    
//     .rvvi ( rvvi )
// );

// // Tie-offs
// assign if_instr_bad_uvc.wdata = '0;
// assign if_instr_bad_uvc.we    = '0;
// // assign if_instr_bad_uvc.be    = 4'b0011;
// assign if_instr_bad_uvc.be    = '1;

core_wrapper #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) wrapper_inst (
    .clk_i      ( clk ),
    .rst_n_i    ( dlyd_rst_n ),
    
    // .if_clknrst(if_clknrst),
    .if_instr_bad_uvc   ( if_instr_bad_uvc ),
    .if_data_bad_uvc    ( if_data_bad_uvc ),
    .if_rvvi            ( if_rvvi ),
    
    .hartid_i       ( hartid ),
    .mtvec_i        ( mtvec ),
    .boot_addr_i    ( boot_addr )
);

// uvm_default_report_server rserver;

//==============   Module instantiations - END   ==============//

//=================   Simulation Variables - BEGIN   =================//

bit    verbose = 0;
string prog_name = "";
string progs_path = "./programs";
string bin_file = {"./mytest/asm_test/", prog_name, ".bin"};

//=================   Simulation Variables - END   =================//

//=================   Simulation - BEGIN   =================//

initial begin
    $timeformat(-9, 3, "ns", 12); // e.g.: "       900ns"
    $dumpfile("dump.vcd");
    $dumpvars;
    
    get_plus_args();
    
    // rserver = uvm_report_server::get_server();

    // Virtual interfaces send to VIPs - begin
        uvm_config_db#(virtual interface clknrst_if)::set(null, "uvm_test_top", "vif_clknrst"      , if_clknrst      );
        uvm_config_db#(virtual interface bad_uvc_if)::set(null, "uvm_test_top", "instr_bad_uvc_vif", if_instr_bad_uvc);
        uvm_config_db#(virtual interface bad_uvc_if)::set(null, "uvm_test_top", "data_bad_uvc_vif" , if_data_bad_uvc );
        uvm_config_db#(virtual interface rvvi_if   )::set(null, "uvm_test_top", "vif_rvvi"         , if_rvvi         );
    // Virtual interfaces send to VIPs - end

    run_test("random_test");
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) dlyd_rst_n <= 1'b0;
    else dlyd_rst_n <= rst_n;
end

//=================   Simulation - END   =================//

//==============   Tasks and functions - BEGIN   ==============//

function void get_plus_args ();
    if ($value$plusargs("prog=%s", prog_name)) begin
        $display("Got prog from plusargs:\n  %s.", prog_name);
    end
    if ($value$plusargs("progs_path=%s", progs_path)) begin
        $display("Got progs_path from plusargs:\n  %s", progs_path);
    end
    if ($value$plusargs("start_addr=%h", fetch_start_addr)) begin
        $display("Got start_addr from plusargs:\n  %h", fetch_start_addr);
    end
    if ($value$plusargs("verbose=%b", verbose)) begin
        $display("Got verbose from plusargs:\n  %b", verbose);
    end
    if ($value$plusargs("bin=%s", bin_file)) begin
        $display("Got bin_file from plusargs:\n  %s.", bin_file);
    end
endfunction

//==============   Tasks and functions - END   ==============//

endmodule: tb_top
