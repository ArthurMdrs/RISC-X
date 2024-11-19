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
//                 Ewerton Cordeiro - jose.cordeiro@ee.ufcg.edu.br            //
//                 Davi Medeiros -                                            //
//                                                                            //
// Design Name:    Instruction decode stage                                   //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decodes instructions and contains the register file.       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module id_stage import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Input from IF stage
    input  logic [31:0] pc_if_i,
    input  logic [31:0] instr_if_i,
    input  logic        valid_if_i,
    input  logic        is_compressed_if_i,
    
    // Output to IF stage
    output logic [31:0] jump_target_id_o,
    output logic        trap_id_o,
    
    // Output to EX stage
    output alu_operation_t  alu_operation_id_o,
    output alu_result_mux_t alu_result_mux_id_o,
    output logic [ 4:0]     rd_addr_id_o,
    output reg_bank_mux_t   rd_dst_bank_id_o,
    output logic            mem_wen_id_o,
    output data_type_t      mem_data_type_id_o,
    output logic            mem_sign_extend_id_o,
    output logic            reg_alu_wen_id_o,
    output logic            reg_mem_wen_id_o,
    output logic [31:0]     pc_id_o,
    output pc_source_t      pc_source_id_o,
    output logic            is_branch_id_o,
    output logic [31:0]     alu_operand_1_id_o,
    output logic [31:0]     alu_operand_2_id_o,
    output logic [31:0]     alu_operand_3_id_o,
    output logic [31:0]     mem_wdata_id_o,
    output logic [31:0]     branch_target_id_o,
    output logic            valid_id_o,
    
    // Input from WB stage
    input  logic [31:0]   reg_wdata_wb_i,
    input  logic [ 4:0]   rd_addr_wb_i,
    input  reg_bank_mux_t rd_dst_bank_wb_i,
    input  logic          reg_wen_wb_i,
    
    // Output to controller
    output logic [ 4:0]   rs1_addr_id_o,
    output logic [ 4:0]   rs2_addr_id_o,
    output logic [ 4:0]   rs3_addr_id_o,
    output reg_bank_mux_t rs1_src_bank_id_o,
    output reg_bank_mux_t rs2_src_bank_id_o,
    output reg_bank_mux_t rs3_src_bank_id_o,
    output logic          rs1_is_used_id_o,
    output logic          rs2_is_used_id_o,
    output logic          rs3_is_used_id_o,
    output logic          illegal_instr_id_o,
    output logic          instr_addr_misaligned_id_o,
    output logic          is_mret_id_o,
    
    // Output to CSRs
    output logic           csr_access_id_o,
    output csr_operation_t csr_op_id_o,
    
    // Control inputs
    input  logic stall_id_i,
    input  logic flush_id_i,
    input  logic branch_decision_ex_i,
    
    // Inputs for forwarding
    input  forward_t    fwd_rs1_id_i,
    input  forward_t    fwd_rs2_id_i,
    input  forward_t    fwd_rs3_id_i,
    input  logic [31:0] alu_result_ex_i,
    input  logic [31:0] alu_result_mem_i,
    input  logic [31:0] mem_rdata_mem_i,
    input  logic [31:0] alu_result_wb_i,
    input  logic [31:0] mem_rdata_wb_i,
    input  logic [31:0] csr_rdata_ex_i,
    
    // FPU signals
    output logic [2:0] fpu_rnd_mode_id_o,
    output logic [3:0] fpu_op_id_o,
    output logic       fpu_op_mod_id_o,
    output logic       fpu_req_id_o,
    
    input  logic fpu_busy_ex_i
    
);

///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION DECODE        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

logic [31:0] instr_id;
logic        is_compressed_id;

logic [31:0] rs1_rdata_id , rs2_rdata_id , rs3_rdata_id ;
logic [31:0] rs1_or_fwd_id, rs2_or_fwd_id, rs3_or_fwd_id;

alu_source_1_t     alu_source_1_id; 
alu_source_2_t     alu_source_2_id; 
alu_source_3_t     alu_source_3_id; 
immediate_source_t immediate_type_id;
logic [31:0]       immediate_id;

logic fpu_req_id_int;

logic exception_id;

`ifdef JASPER
`default_nettype none
`endif

// Pipeline registers IF->ID
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        pc_id_o  <= '0;
        instr_id <= '0;
        valid_id_o <= '0;
        is_compressed_id <= '0;
    end else begin
        if (!stall_id_i) begin
            // Insert bubble if flushing is needed
            if (flush_id_i) begin
                instr_id <= 32'h0000_0013; // NOP instruction
                valid_id_o <= 1'b0;
                is_compressed_id <= '0;
            end
            else begin
                pc_id_o  <= pc_if_i;
                instr_id <= instr_if_i;
                valid_id_o <= valid_if_i;
                is_compressed_id <= is_compressed_if_i;
            end
        end
    end
end

decoder #(
    .ISA_M ( ISA_M ),
    .ISA_C ( ISA_C ),
    .ISA_F ( ISA_F )
) decoder_inst (
    // ALU related signals
    .alu_operation_o  ( alu_operation_id_o ),
    .alu_source_1_o   ( alu_source_1_id ), 
    .alu_source_2_o   ( alu_source_2_id ), 
    .alu_source_3_o   ( alu_source_3_id ), 
    .immediate_type_o ( immediate_type_id ),
    .alu_result_mux_o ( alu_result_mux_id_o ),
    
    // Source/destiny general purpose registers
    .rs1_addr_o     ( rs1_addr_id_o ),
    .rs2_addr_o     ( rs2_addr_id_o ),
    .rs3_addr_o     ( rs3_addr_id_o ),
    .rd_addr_o      ( rd_addr_id_o ),
    .rs1_src_bank_o ( rs1_src_bank_id_o ),
    .rs2_src_bank_o ( rs2_src_bank_id_o ),
    .rs3_src_bank_o ( rs3_src_bank_id_o ),
    .rd_dst_bank_o  ( rd_dst_bank_id_o ),
    .rs1_is_used_o  ( rs1_is_used_id_o ),
    .rs2_is_used_o  ( rs2_is_used_id_o ),
    .rs3_is_used_o  ( rs3_is_used_id_o ),
    
    // Memory access related signals
    .mem_wen_o         ( mem_wen_id_o ),
    .mem_data_type_o   ( mem_data_type_id_o ),
    .mem_sign_extend_o ( mem_sign_extend_id_o ),
    
    // Write enable for ALU and mem access operations
    .reg_alu_wen_o ( reg_alu_wen_id_o ), 
    .reg_mem_wen_o ( reg_mem_wen_id_o ), 
    
    // Control transfer related signals
    .pc_source_o ( pc_source_id_o ), 
    .is_branch_o ( is_branch_id_o ),
    
    // CSR related signals
    .csr_access_o ( csr_access_id_o ),
    .csr_op_o     ( csr_op_id_o ),
    
    // Indicate MRET
    .is_mret_o ( is_mret_id_o ),
    
    // Decoded an illegal instruction
    .illegal_instr_o ( illegal_instr_id_o ),
    
    // Instruction to be decoded
    .instr_i         ( instr_id ),
    .is_compressed_i ( is_compressed_id ),
    
    // FPU signals
    .fpu_rnd_mode_o ( fpu_rnd_mode_id_o ),
    .fpu_op_o       ( fpu_op_id_o ),
    .fpu_op_mod_o   ( fpu_op_mod_id_o ),
    .fpu_req_o      ( fpu_req_id_int )
);

imm_extender imm_extender_inst (
    .immediate        ( immediate_id ),
    .immediate_type_i ( immediate_type_id ),
    .instr_i          ( instr_id )
);

register_file #(
    .GEN_F_REGS ( ISA_F )
) register_file_inst (
    .clk_i    ( clk_i ),
    .rst_n_i  ( rst_n_i ),
    
    .wdata_i  ( reg_wdata_wb_i ),
    .waddr_i  ( rd_addr_wb_i ),
    .wen_i    ( reg_wen_wb_i ),
    .wdst_i   ( rd_dst_bank_wb_i ),
    
    .rdata1_o ( rs1_rdata_id ),
    .rdata2_o ( rs2_rdata_id ),
    .rdata3_o ( rs3_rdata_id ),
    .raddr1_i ( rs1_addr_id_o ),
    .raddr2_i ( rs2_addr_id_o ),
    .raddr3_i ( rs3_addr_id_o ),
    .rsrc1_i  ( rs1_src_bank_id_o ),
    .rsrc2_i  ( rs2_src_bank_id_o ),
    .rsrc3_i  ( rs3_src_bank_id_o )
    
);

// Resolve forwarding for source registers
always_comb begin
    unique case (fwd_rs1_id_i)
        NO_FORWARD           : rs1_or_fwd_id = rs1_rdata_id;
        FWD_EX_ALU_RES_TO_ID : rs1_or_fwd_id = alu_result_ex_i;
        FWD_MEM_ALU_RES_TO_ID: rs1_or_fwd_id = alu_result_mem_i;
        FWD_MEM_RDATA_TO_ID  : rs1_or_fwd_id = mem_rdata_mem_i;
        FWD_WB_ALU_RES_TO_ID : rs1_or_fwd_id = alu_result_wb_i;
        FWD_WB_RDATA_TO_ID   : rs1_or_fwd_id = mem_rdata_wb_i;
        default: rs1_or_fwd_id = rs1_rdata_id;
    endcase
    unique case (fwd_rs2_id_i)
        NO_FORWARD           : rs2_or_fwd_id = rs2_rdata_id;
        FWD_EX_ALU_RES_TO_ID : rs2_or_fwd_id = alu_result_ex_i;
        FWD_MEM_ALU_RES_TO_ID: rs2_or_fwd_id = alu_result_mem_i;
        FWD_MEM_RDATA_TO_ID  : rs2_or_fwd_id = mem_rdata_mem_i;
        FWD_WB_ALU_RES_TO_ID : rs2_or_fwd_id = alu_result_wb_i;
        FWD_WB_RDATA_TO_ID   : rs2_or_fwd_id = mem_rdata_wb_i;
        default: rs2_or_fwd_id = rs2_rdata_id;
    endcase
    unique case (fwd_rs3_id_i)
        NO_FORWARD           : rs3_or_fwd_id = rs3_rdata_id;
        FWD_EX_ALU_RES_TO_ID : rs3_or_fwd_id = alu_result_ex_i;
        FWD_MEM_ALU_RES_TO_ID: rs3_or_fwd_id = alu_result_mem_i;
        FWD_MEM_RDATA_TO_ID  : rs3_or_fwd_id = mem_rdata_mem_i;
        FWD_WB_ALU_RES_TO_ID : rs3_or_fwd_id = alu_result_wb_i;
        FWD_WB_RDATA_TO_ID   : rs3_or_fwd_id = mem_rdata_wb_i;
        default: rs3_or_fwd_id = rs3_rdata_id;
    endcase
end

// ALU operands
always_comb begin
    unique case (alu_source_1_id)
        ALU_SCR1_RS1    : alu_operand_1_id_o = rs1_or_fwd_id;
        ALU_SCR1_PC     : alu_operand_1_id_o = pc_id_o;
        ALU_SCR1_ZERO   : alu_operand_1_id_o = 32'b0;
        ALU_SCR1_IMM_CSR: alu_operand_1_id_o = {27'b0, instr_id[19:15]}; // Pass CSR wdata as ALU operand
        default: alu_operand_1_id_o = 32'b0;
    endcase
    unique case (alu_source_2_id)
        ALU_SCR2_RS1   : alu_operand_2_id_o = rs1_or_fwd_id;
        ALU_SCR2_RS2   : alu_operand_2_id_o = rs2_or_fwd_id;
        ALU_SCR2_IMM   : alu_operand_2_id_o = immediate_id;
        ALU_SCR2_4_OR_2: alu_operand_2_id_o = (is_compressed_id) ? (32'd2) : (32'd4);
        default: alu_operand_2_id_o = 32'b0;
    endcase
    unique case (alu_source_3_id)
        ALU_SCR3_RS2   : alu_operand_3_id_o = rs2_or_fwd_id;
        ALU_SCR3_RS3   : alu_operand_3_id_o = rs3_or_fwd_id;
        default: alu_operand_3_id_o = 32'b0;
    endcase
end

// Pass forward the data to write in the memory
assign mem_wdata_id_o = rs2_or_fwd_id;

// Calculate branch target
assign branch_target_id_o = pc_id_o + immediate_id;

// Calculate jump target
always_comb begin
    unique case (pc_source_id_o)
        PC_JAL : jump_target_id_o = pc_id_o + immediate_id;
        PC_JALR: jump_target_id_o = rs1_or_fwd_id + immediate_id;
        default: jump_target_id_o = pc_id_o + immediate_id;
    endcase
    jump_target_id_o[0] = 1'b0; // Clear LSB
end

// Jump target misaligned exception
always_comb begin
    if (ISA_C) // No such exceptions if compressed instructions are allowed
        instr_addr_misaligned_id_o = 1'b0;
    else // If no compressed instructions, target must be 4-byte aligned
        instr_addr_misaligned_id_o = jump_target_id_o[1] && (pc_source_id_o inside {PC_JAL, PC_JALR});
end

// Deassert FPU req if we don't have a valid instruction
// assign fpu_req_id_o = fpu_req_id_int && valid_id_o && !illegal_instr_id_o && !flush_ex_i; // && !stall_ex_i;
// assign fpu_req_id_o = fpu_req_id_int && valid_id_o && !illegal_instr_id_o && !branch_decision_ex_i && !stall_id_i;
assign fpu_req_id_o = fpu_req_id_int && valid_id_o && !illegal_instr_id_o && !branch_decision_ex_i && !fpu_busy_ex_i;

// Traps: illegal instruction decoded, jump target misaligned, mret
assign exception_id = illegal_instr_id_o || instr_addr_misaligned_id_o || is_mret_id_o;
assign trap_id_o = valid_id_o && exception_id;

`ifdef JASPER
`default_nettype wire
`endif

endmodule