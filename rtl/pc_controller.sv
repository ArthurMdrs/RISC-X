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
// Design Name:    PC controller                                              //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decides next PC based on core's state.                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module pc_controller import core_pkg::*; #(
    parameter int WIDTH = 32
) (
    output logic [WIDTH-1:0] next_pc_o,
    input  logic [WIDTH-1:0] curr_pc_i, 
    input  logic             valid_id_i,
    input  logic [WIDTH-1:0] jump_target_id_i, 
    input  logic [WIDTH-1:0] branch_target_ex_i, 
    input  logic             branch_decision_ex_i,
    input  logic             is_compressed_if_i,
    input  pc_source_t       pc_source_id_i,
    input  pc_source_t       pc_source_ex_i,
    input                    trap_id_i,
    input                    trap_ex_i,
    
    input                    is_mret_i,
    input  logic [WIDTH-1:0] mtvec_i,
    input  logic [WIDTH-1:0] mepc_i
);

next_pc_mux_t next_pc_mux;
exc_pc_mux_t  exc_pc_mux;
logic [31:0]  exc_pc;

`ifdef JASPER
`default_nettype none
`endif

// Determine the select signal for the next PC mux
always_comb begin
    if (trap_ex_i)
        next_pc_mux = NPC_EXCEPTION;
    else if ((pc_source_ex_i == PC_BRANCH) && branch_decision_ex_i)
        next_pc_mux = NPC_BRANCH;
    else if (trap_id_i)
        next_pc_mux = NPC_EXCEPTION;
    else if (pc_source_id_i == PC_JAL || pc_source_id_i == PC_JALR)
        next_pc_mux = NPC_JUMP;
    else if (is_compressed_if_i)
        next_pc_mux = NPC_P_2;
    else
        next_pc_mux = NPC_P_4;
end

// Determine the select signal for the exception PC mux
always_comb begin
    if (is_mret_i)
        exc_pc_mux = EXCPC_MEPC;
    else
        exc_pc_mux = EXCPC_MTVEC;
end

// Determine the exception address
always_comb begin
    unique case (exc_pc_mux)
        EXCPC_MTVEC: exc_pc = mtvec_i;
        EXCPC_MEPC : exc_pc = mepc_i;
        default: exc_pc = mtvec_i;
    endcase
end

// Determine next instruction address (PC)
always_comb begin
    unique case (next_pc_mux)
        NPC_P_4      : next_pc_o = curr_pc_i + 32'd4;
        NPC_P_2      : next_pc_o = curr_pc_i + 32'd2;
        NPC_JUMP     : next_pc_o = jump_target_id_i;
        NPC_BRANCH   : next_pc_o = branch_target_ex_i;
        NPC_EXCEPTION: next_pc_o = exc_pc;
        default: next_pc_o = curr_pc_i + 32'd4;
    endcase
end

`ifdef JASPER
`default_nettype wire
`endif

endmodule