// Copyright 2024 UFCG
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Author:         Pedro Medeiros - pedromedeiros.egnr@gmail.com              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Design Name:    Testbench top                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Testbench top module that runs an UVM test.                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

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

// The start of .text will be the core's first fetch
int fetch_start_addr = 32'h0000_3000;

wire [31:0] hartid    = 32'h0000_0000;
wire [23:0] mtvec     = 24'h8000_80;
wire [29:0] boot_addr = fetch_start_addr[31:2];

assign clk   = if_clknrst.clk;
assign rst_n = if_clknrst.rst_n;

// Interfaces instances - begin
    clknrst_if                  if_clknrst      ();
    obi_if                      if_instr_obi    (.clk(clk), .rst_n(rst_n));
    obi_if                      if_data_obi     (.clk(clk), .rst_n(rst_n));
    rvvi_if#(ILEN,XLEN,FLEN)    if_rvvi         (.clk(clk), .rst_n(rst_n));
// Interfaces instances - end

//==============   Module instantiations - BEGIN   ==============//

core_wrapper #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) wrapper_inst (
    .clk_i      ( clk ),
    .rst_n_i    ( rst_n ),
    
    // .if_clknrst(if_clknrst),
    .if_instr_obi   ( if_instr_obi ),
    .if_data_obi    ( if_data_obi ),
    .if_rvvi        ( if_rvvi ),
    
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
        uvm_config_db#(virtual interface clknrst_if)::set(null, "uvm_test_top", "vif_clknrst"  , if_clknrst  );
        uvm_config_db#(virtual interface obi_if    )::set(null, "uvm_test_top", "instr_obi_vif", if_instr_obi);
        uvm_config_db#(virtual interface obi_if    )::set(null, "uvm_test_top", "data_obi_vif" , if_data_obi );
        uvm_config_db#(virtual interface rvvi_if   )::set(null, "uvm_test_top", "vif_rvvi"     , if_rvvi     );
    // Virtual interfaces send to VIPs - end

    run_test("random_test");
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
