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
// Design Name:    RVFI Wrapper                                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    RVFI Wrapper that includes the core and RVFI.              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module rvfi_wrapper (
    input logic clock,
    input logic reset
    ,
    `RVFI_OUTPUTS
);

// logic [ 4:0] rvfi_frs1_addr;
// logic [ 4:0] rvfi_frs2_addr;
// logic [ 4:0] rvfi_frs3_addr;
logic [ 4:0] rvfi_frd_addr;
// logic rvfi_frs1_rvalid;
// logic rvfi_frs2_rvalid;
// logic rvfi_frs3_rvalid;
logic        rvfi_frd_wvalid;
// logic [31:0] rvfi_frs1_rdata;
// logic [31:0] rvfi_frs2_rdata;
// logic [31:0] rvfi_frs3_rdata;
logic [31:0] rvfi_frd_wdata;
    
// Outputs:         (* keep *)               wire
// Tied-off inputs: (* keep *)               wire
// Random inputs:   (* keep *) `rvformal_rand_reg

////////////////////   PORT LIST - BEGIN   ////////////////////

// Primary inputs
(* keep *) wire clk_i;
(* keep *) wire rst_n_i;

// Data memory interface
(* keep *) `rvformal_rand_reg [31:0] dmem_rdata;
(* keep *)               wire [31:0] dmem_wdata;
(* keep *)               wire [31:0] dmem_addr;
(* keep *)               wire        dmem_wen;
(* keep *)               wire  [3:0] dmem_ben;

// Instruction memory interface
(* keep *) `rvformal_rand_reg [31:0] imem_rdata;
(* keep *)               wire [31:0] imem_addr;

(* keep *)               wire [31:0] hartid;
(* keep *)               wire [23:0] mtvec;
(* keep *)               wire [29:0] boot_addr;
    
////////////////////    PORT LIST - END    ////////////////////

`ifdef JASPER
`default_nettype none
`endif
    
// Tie-offs
assign clk_i   = clock;
assign rst_n_i = !reset;

assign hartid    = 32'h0000_0000;
assign mtvec     = 24'h0000_80;
assign boot_addr = 30'h0000_0c00; // Equivalent to 32'b0000_3000;

localparam bit ISA_C = 1;
localparam bit ISA_M = 0;
localparam bit ISA_F = 1;

core #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) core_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    .dmem_rdata_i ( dmem_rdata ),
    .dmem_wdata_o ( dmem_wdata ),
    .dmem_addr_o  ( dmem_addr ),
    .dmem_wen_o   ( dmem_wen ),
    .dmem_ben_o   ( dmem_ben ),
    
    .imem_rdata_i ( imem_rdata ),
    .imem_addr_o  ( imem_addr ),
    
    .hartid_i    ( hartid ),
    .mtvec_i     ( mtvec ),
    .boot_addr_i ( boot_addr )
);

`include "rvfi_inst.sv"

`ifdef JASPER
`default_nettype wire
`endif

endmodule

