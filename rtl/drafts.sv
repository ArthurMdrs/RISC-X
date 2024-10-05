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
logic ctrl_transfer, ctrl_transfer_q;
logic obi_tr_cnt;
logic core_ready;

`ifdef JASPER
`default_nettype none
`endif

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

always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        ctrl_transfer_q <= 1'b0;
    end else begin
        if (insn_obi_rvalid_i && (obi_tr_cnt != '0)) begin
            ctrl_transfer_q <= 1'b0;
        end
        else if (ctrl_transfer) begin
            ctrl_transfer_q <= 1'b1;
        end
    end
end

// Count transactions (max 1 outstanding)
wire obi_tr_cnt_up = insn_obi_req_o    && insn_obi_gnt_i   ;
wire obi_tr_cnt_dn = insn_obi_rvalid_i && insn_obi_rready_o && (obi_tr_cnt != '0);
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        obi_tr_cnt <= 1'b0;
    end else begin
        unique case ({obi_tr_cnt_up, obi_tr_cnt_dn})
            2'b00: obi_tr_cnt <= obi_tr_cnt;        // No  new input tr, no output done
            2'b01: obi_tr_cnt <= obi_tr_cnt - 1;    // No  new input tr,    output done
            2'b10: obi_tr_cnt <= obi_tr_cnt + 1;    // Got new input tr, no output done
            2'b11: obi_tr_cnt <= obi_tr_cnt;        // Got new input tr,    output done
            default: obi_tr_cnt <= '0;
        endcase
    end
end

// Determine next instruction address (PC)
pc_controller pc_controller_inst (
    .next_pc_o            ( pc_if_n ),
    .ctrl_transfer_o      ( ctrl_transfer ),
    
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
    .resp_valid_o           ( valid_if_o ),
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
    .obi_rready_o           ( insn_obi_rready_o ),
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

`ifdef JASPER
`default_nettype wire
`endif

endmodule

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
    output logic             ctrl_transfer_o,
    
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
    input                    core_ready_i,
    
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
    ctrl_transfer_o = 1'b1;
    
    if (trap_ex_i) begin
        next_pc_mux = NPC_EXCEPTION;
    end
    else if ((pc_source_ex_i == PC_BRANCH) && branch_decision_ex_i) begin
        next_pc_mux = NPC_BRANCH;
    end
    else if (trap_id_i) begin
        next_pc_mux = NPC_EXCEPTION;
    end
    else if (pc_source_id_i == PC_JAL || pc_source_id_i == PC_JALR) begin
        next_pc_mux = NPC_JUMP;
    end
    else if (is_compressed_if_i) begin
        next_pc_mux = NPC_P_2;
        ctrl_transfer_o = 1'b0;
    end
    else begin
        next_pc_mux = NPC_P_4;
        ctrl_transfer_o = 1'b0;
    end
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
        // NPC_REPEAT   : next_pc_o = curr_pc_i;
        default: next_pc_o = curr_pc_i + 32'd4;
    endcase
end

`ifdef JASPER
`default_nettype wire
`endif

endmodule