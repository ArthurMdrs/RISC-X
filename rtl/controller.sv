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
// Design Name:    Main controller                                            //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor.                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module controller import core_pkg::*; (
    // Data Hazards (forwarding)
    output forward_t fwd_rs1_o,
    output forward_t fwd_rs2_o,
    output forward_t fwd_rs3_o,
    // Source/destiny general purpose registers
    input  logic [4:0] rs1_addr_id_i,
    input  logic [4:0] rs2_addr_id_i,
    input  logic [4:0] rs3_addr_id_i,
    input  logic [4:0] rd_addr_ex_i,
    input  logic [4:0] rd_addr_mem_i,
    input  logic [4:0] rd_addr_wb_i,
    // Write enables
    input  logic reg_alu_wen_ex_i,
    input  logic reg_alu_wen_mem_i,
    input  logic reg_alu_wen_wb_i,
    input  logic reg_mem_wen_ex_i,
    input  logic reg_mem_wen_mem_i,
    input  logic reg_mem_wen_wb_i,
    // Type of register (x or f)
    input  reg_bank_mux_t rs1_src_bank_id_i,
    input  reg_bank_mux_t rs2_src_bank_id_i,
    input  reg_bank_mux_t rs3_src_bank_id_i,
    input  reg_bank_mux_t rd_dst_bank_ex_i,
    input  reg_bank_mux_t rd_dst_bank_mem_i,
    input  reg_bank_mux_t rd_dst_bank_wb_i,
    
    // Data Hazards (stalling)
    output logic stall_if_o,
    output logic stall_id_o,
    output logic stall_ex_o,
    output logic stall_mem_o,
    input  logic fpu_req_id_i,
    input  logic fpu_gnt_id_i,
    input  logic fpu_busy_ex_i,
    input  logic data_obi_busy_mem_i,
    
    // Control Hazards (flushing)
    output logic flush_id_o,
    output logic flush_ex_o,
    output logic flush_mem_o,
    output logic flush_wb_o,
    input  pc_source_t pc_source_id_i,
    input  logic       branch_decision_ex_i,
    input  logic valid_if_i,
    input  logic trap_id_i,
    input  logic trap_ex_i,
    
    // Trap handling
    output logic       save_pc_id_o, // Save ID PC to mepc
    output logic       save_pc_ex_o, // Save EX PC to mepc
    input  logic       illegal_instr_id_i,
    input  logic       instr_addr_misaligned_id_i,
    // input  logic       instr_addr_misaligned_ex_i,
    input  logic       is_mret_id_i,
    output logic [4:0] exception_cause_o // Exception cause code for mcause
);

logic rd_ex_valid ;
logic rd_mem_valid;
logic rd_wb_valid ;

logic rd_ex_is_rs1_id ;
logic rd_mem_is_rs1_id;
logic rd_wb_is_rs1_id ;

logic rd_ex_is_rs2_id ;
logic rd_mem_is_rs2_id;
logic rd_wb_is_rs2_id ;

logic rd_ex_is_rs3_id ;
logic rd_mem_is_rs3_id;
logic rd_wb_is_rs3_id ;

logic fpu_gnt_stall;
logic fpu_rvalid_stall;

`ifdef JASPER
`default_nettype none
`endif

assign rd_ex_valid  = (rd_dst_bank_ex_i  == X_REG && rd_addr_ex_i  != '0) || (rd_dst_bank_ex_i  == F_REG);
assign rd_mem_valid = (rd_dst_bank_mem_i == X_REG && rd_addr_mem_i != '0) || (rd_dst_bank_mem_i == F_REG);
assign rd_wb_valid  = (rd_dst_bank_wb_i  == X_REG && rd_addr_wb_i  != '0) || (rd_dst_bank_wb_i  == F_REG);

assign rd_ex_is_rs1_id  = (rd_addr_ex_i  == rs1_addr_id_i) && (rd_ex_valid ) && (rd_dst_bank_ex_i  == rs1_src_bank_id_i);
assign rd_mem_is_rs1_id = (rd_addr_mem_i == rs1_addr_id_i) && (rd_mem_valid) && (rd_dst_bank_mem_i == rs1_src_bank_id_i);
assign rd_wb_is_rs1_id  = (rd_addr_wb_i  == rs1_addr_id_i) && (rd_wb_valid ) && (rd_dst_bank_wb_i  == rs1_src_bank_id_i);

assign rd_ex_is_rs2_id  = (rd_addr_ex_i  == rs2_addr_id_i) && (rd_ex_valid ) && (rd_dst_bank_ex_i  == rs2_src_bank_id_i);
assign rd_mem_is_rs2_id = (rd_addr_mem_i == rs2_addr_id_i) && (rd_mem_valid) && (rd_dst_bank_mem_i == rs2_src_bank_id_i);
assign rd_wb_is_rs2_id  = (rd_addr_wb_i  == rs2_addr_id_i) && (rd_wb_valid ) && (rd_dst_bank_wb_i  == rs2_src_bank_id_i);

assign rd_ex_is_rs3_id  = (rd_addr_ex_i  == rs3_addr_id_i) && (rd_ex_valid ) && (rd_dst_bank_ex_i  == rs3_src_bank_id_i);
assign rd_mem_is_rs3_id = (rd_addr_mem_i == rs3_addr_id_i) && (rd_mem_valid) && (rd_dst_bank_mem_i == rs3_src_bank_id_i);
assign rd_wb_is_rs3_id  = (rd_addr_wb_i  == rs3_addr_id_i) && (rd_wb_valid ) && (rd_dst_bank_wb_i  == rs3_src_bank_id_i);

assign fpu_gnt_stall    = fpu_req_id_i && !fpu_gnt_id_i;
assign fpu_rvalid_stall = fpu_busy_ex_i;

logic id_is_jump;
logic ctrl_transfer;

assign id_is_jump = pc_source_id_i == PC_JAL || pc_source_id_i == PC_JALR;
assign ctrl_transfer = branch_decision_ex_i || id_is_jump || trap_id_i;

// Resolve forwarding for rs1
always_comb begin
    fwd_rs1_o = NO_FORWARD;
    if (rd_ex_is_rs1_id && reg_alu_wen_ex_i) begin
        fwd_rs1_o = FWD_EX_ALU_RES_TO_ID;
    end
    else if (rd_mem_is_rs1_id && (reg_alu_wen_mem_i || reg_mem_wen_mem_i)) begin
        if (reg_alu_wen_mem_i)
            fwd_rs1_o = FWD_MEM_ALU_RES_TO_ID;
        else if (reg_mem_wen_mem_i)
            fwd_rs1_o = FWD_MEM_RDATA_TO_ID;
    end
    else if (rd_wb_is_rs1_id && (reg_alu_wen_wb_i || reg_mem_wen_wb_i)) begin
        if (reg_alu_wen_wb_i)
            fwd_rs1_o = FWD_WB_ALU_RES_TO_ID;
        else if (reg_mem_wen_wb_i)
            fwd_rs1_o = FWD_WB_RDATA_TO_ID;
    end
end

// Resolve forwarding for rs2
always_comb begin
    fwd_rs2_o = NO_FORWARD;
    if (rd_ex_is_rs2_id && reg_alu_wen_ex_i) begin
        fwd_rs2_o = FWD_EX_ALU_RES_TO_ID;
    end
    else if (rd_mem_is_rs2_id && (reg_alu_wen_mem_i || reg_mem_wen_mem_i)) begin
        if (reg_alu_wen_mem_i)
            fwd_rs2_o = FWD_MEM_ALU_RES_TO_ID;
        else if (reg_mem_wen_mem_i)
            fwd_rs2_o = FWD_MEM_RDATA_TO_ID;
    end
    else if (rd_wb_is_rs2_id && (reg_alu_wen_wb_i || reg_mem_wen_wb_i)) begin
        if (reg_alu_wen_wb_i)
            fwd_rs2_o = FWD_WB_ALU_RES_TO_ID;
        else if (reg_mem_wen_wb_i)
            fwd_rs2_o = FWD_WB_RDATA_TO_ID;
    end
end

// Resolve forwarding for rs3
always_comb begin
    fwd_rs3_o = NO_FORWARD;
    if (rd_ex_is_rs3_id && reg_alu_wen_ex_i) begin
        fwd_rs3_o = FWD_EX_ALU_RES_TO_ID;
    end
    else if (rd_mem_is_rs3_id && (reg_alu_wen_mem_i || reg_mem_wen_mem_i)) begin
        if (reg_alu_wen_mem_i)
            fwd_rs3_o = FWD_MEM_ALU_RES_TO_ID;
        else if (reg_mem_wen_mem_i)
            fwd_rs3_o = FWD_MEM_RDATA_TO_ID;
    end
    else if (rd_wb_is_rs3_id && (reg_alu_wen_wb_i || reg_mem_wen_wb_i)) begin
        if (reg_alu_wen_wb_i)
            fwd_rs3_o = FWD_WB_ALU_RES_TO_ID;
        else if (reg_mem_wen_wb_i)
            fwd_rs3_o = FWD_WB_RDATA_TO_ID;
    end
end

// Resolve stalls
always_comb begin
    stall_mem_o = data_obi_busy_mem_i;
    
    stall_ex_o = stall_mem_o || fpu_rvalid_stall;
    
    stall_id_o = stall_ex_o;
    if (fpu_gnt_stall)
        stall_id_o = 1'b1;
    if (reg_mem_wen_ex_i) // Load operation in EX
        if(rd_ex_is_rs1_id || rd_ex_is_rs2_id || rd_ex_is_rs3_id)
            stall_id_o = 1'b1;
    
    stall_if_o = stall_id_o || (!valid_if_i && !ctrl_transfer);
end

// Resolve flushing
always_comb begin
    flush_wb_o  = stall_mem_o;
    // flush_mem_o = flush_wb_o  || trap_ex_i || stall_ex_o;
    flush_mem_o = trap_ex_i || stall_ex_o;
    flush_ex_o  = flush_mem_o || branch_decision_ex_i || stall_id_o || trap_id_i;
    flush_id_o  = flush_ex_o  || id_is_jump || stall_if_o;
end

// Determine which PC should be saved to mepc in case of traps
// Also determine exception cause
always_comb begin
    save_pc_ex_o = 1'b0;
    save_pc_id_o = 1'b0;
    exception_cause_o = 5'b0;
    
    if (trap_ex_i) begin
        save_pc_ex_o = 1'b1;
        exception_cause_o = EXC_CAUSE_INSTR_ADDR_MISAL;
    end
    else if (trap_id_i && !branch_decision_ex_i && !is_mret_id_i) begin
        save_pc_id_o = 1'b1;
        if (illegal_instr_id_i)
            exception_cause_o = EXC_CAUSE_ILLEGAL_INSN;
        else if (instr_addr_misaligned_id_i)
            exception_cause_o = EXC_CAUSE_INSTR_ADDR_MISAL;
    end
end

`ifdef JASPER
`default_nettype wire
`endif

endmodule
