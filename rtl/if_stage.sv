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
//                 Túlio Tavares -                                            //
//                 Victor Melquíades -                                        //
//                                                                            //
// Design Name:    Instruction fetch stage                                    //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Fetches instructions from memory and decides the next PC.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module if_stage import core_pkg::*; (
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic [29:0] boot_addr_i,
    
    // Interface with instruction memory
    // input  logic [31:0] imem_rdata_i,
    // output logic [31:0] imem_addr_o,
    
    // OBI interface for instruction memory
    output logic        insn_obi_req_o,
    input  logic        insn_obi_gnt_i,
    output logic [31:0] insn_obi_addr_o,
    output logic        insn_obi_we_o,
    output logic [ 3:0] insn_obi_be_o,
    output logic [31:0] insn_obi_wdata_o,
    input  logic        insn_obi_rvalid_i,
    output logic        insn_obi_rready_o,
    input  logic [31:0] insn_obi_rdata_i,

    
    // Output to ID stage
    output logic [31:0] pc_if_o,
    output logic [31:0] instr_if_o,
    output logic        valid_if_o,
    output logic        is_compressed_if_o,
    
    // Control inputs
    input  logic stall_if_i,
    
    // Trap handling
    input               trap_id_i,
    input               trap_ex_i,
    input               is_mret_i,
    input  logic [31:0] mtvec_i,
    input  logic [31:0] mepc_i,
    
    // Signals for the PC controller
    input  logic        valid_id_i,
    input  logic        valid_ex_i,
    input  logic [31:0] jump_target_id_i, 
    input  logic [31:0] branch_target_ex_i, 
    input  logic        branch_decision_ex_i,
    input  pc_source_t  pc_source_id_i,
    input  pc_source_t  pc_source_ex_i
);

///////////////////////////////////////////////////////////////////////////////
///////////////////////        INSTRUCTION FETCH        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic [31:0] pc_if_n;
logic core_ready;

// Indicator of compressed instructions
assign is_compressed_if_o = ~(instr_if_o[1] && instr_if_o[0]);
    
// Instruction Memory Interface
//assign instr_if_o = imem_rdata_i; // Instruction read from memory
// assign imem_addr_o = pc_if_o;     // Address from which the instruction is fetched

// Pipeline registers ->IF
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        pc_if_o <= {boot_addr_i, 2'b0};
    end else begin
        if (!stall_if_i) begin
            pc_if_o <= pc_if_n;
        end
    end
end

// Determine next instruction address (PC)
pc_controller pc_controller_inst (
    .next_pc_o            ( pc_if_n ),
    .curr_pc_i            ( pc_if_o ), 
    .valid_id_i           ( valid_id_i ),
    .jump_target_id_i     ( jump_target_id_i ), 
    .branch_target_ex_i   ( branch_target_ex_i ), 
    .branch_decision_ex_i ( branch_decision_ex_i ),
    .is_compressed_if_i   ( is_compressed_if_o),
    .pc_source_id_i       ( pc_source_id_i ),
    .pc_source_ex_i       ( pc_source_ex_i ),
    .trap_id_i            ( trap_id_i ),
    .trap_ex_i            ( trap_ex_i ),
    .core_ready_i         ( core_ready ),
    
    .is_mret_i            ( is_mret_i ),
    .mtvec_i              ( mtvec_i ),
    .mepc_i               ( mepc_i )
);

OBI_controller OBI_controller_inst (
    .clk                    ( clk_i ),
    .rst_n                  ( rst_n_i ),

    // Transaction request interface
    .core_rready_i          ( 1'b1 ),
    .core_valid_i           ( 1'b1 ),
    .core_ready_o           ( core_ready ),
    .core_addr_i            ( pc_if_o ),
    .core_we_i              ( 1'b0 ),
    .core_be_i              ( 4'b1111 ),
    .core_wdata_i           ( 32'b0 ),

    // Transaction response interface
    .resp_valid_o           ( valid_if_o ),  // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
    .resp_rdata_o           ( instr_if_o ),
    .resp_err_o             (  ),

    // OBI interface
    .obi_req_o              ( insn_obi_req_o ),
    .obi_gnt_i              ( insn_obi_gnt_i ),
    .obi_addr_o             ( insn_obi_addr_o ),
    .obi_we_o               ( insn_obi_we_o ),
    .obi_be_o               ( insn_obi_be_o ),
    .obi_wdata_o            ( insn_obi_wdata_o ),
    .obi_atop_o             (  ),
    .obi_rdata_i            ( insn_obi_rdata_i ),
    .obi_rvalid_i           ( insn_obi_rvalid_i ),
    .obi_err_i              ( 1'b0 )

);




// Resolve validness. Not valid implies inserting bubble
// assign valid_if_o = 1'b1;


`ifdef SVA_ON

    // Instruction interface assertions
    assert property (@(posedge clk_i) disable iff (!rst_n_i) insn_obi_req_o |-> ##[1:$] insn_obi_gnt_i);
    assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && !insn_obi_gnt_i |=> $stable(insn_obi_addr_o)));
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && !insn_obi_gnt_i |=> $stable(insn_obi_we_o)));
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && !insn_obi_gnt_i |=> $stable(insn_obi_be_o)));
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && !insn_obi_gnt_i |=> $stable(insn_obi_wdata_o)));
    assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && !insn_obi_gnt_i |=> insn_obi_req_o));

    assert property (@(posedge clk_i) disable iff (!rst_n_i) insn_obi_rvalid_i |-> ##[1:$] insn_obi_rready_o);
    // Asserts below should be assumes?
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_rvalid_i && !insn_obi_rready_o |=> $stable(insn_obi_rdata)));
    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_rvalid_i && !insn_obi_rready_o |=> insn_obi_rvalid_i));

    // assert property (@(posedge clk_i) disable iff (!rst_n_i) (insn_obi_req_o && insn_obi_gnt_i && insn_obi_we |-> insn_obi_be != '0));

`endif

endmodule