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
// Design Name:    Instantiation of RVFI module                               //
// Project Name:   RISC-X                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Include this with `include macro. There must be local      //
//                 signals called clk_i and rst_n_i.                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// This file is meant to be included using the `include directive

rvfi rvfi_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Input from IF stage
    .valid_if    ( core_inst.valid_if ),
    .stall_if    ( core_inst.stall_if ),
    .pc_if       ( core_inst.pc_if ),
    .next_pc_mux ( core_inst.if_stage_inst.pc_controller_inst.next_pc_mux ),
    
    // Input from ID stage
    .valid_id         ( core_inst.valid_id ),
    .stall_id         ( core_inst.stall_id ),
    .flush_id         ( core_inst.flush_id ),
    .trap_id          ( core_inst.trap_id ),
    .instr_id         ( core_inst.id_stage_inst.instr_id ),
    .illegal_instr_id ( core_inst.illegal_instr_id ),
    .alu_source_1_id  ( core_inst.id_stage_inst.alu_source_1_id ),
    .alu_source_2_id  ( core_inst.id_stage_inst.alu_source_2_id ),
    .alu_source_3_id  ( core_inst.id_stage_inst.alu_source_3_id ),
    .rs1_addr_id      ( core_inst.rs1_addr_id ),
    .rs2_addr_id      ( core_inst.rs2_addr_id ),
    .rs3_addr_id      ( core_inst.rs3_addr_id ),
    .rs1_src_bank_id  ( core_inst.rs1_src_bank_id ),
    .rs2_src_bank_id  ( core_inst.rs2_src_bank_id ),
    .rs3_src_bank_id  ( core_inst.rs3_src_bank_id ),
    .rs1_is_used_id   ( core_inst.rs1_is_used_id ),
    .rs2_is_used_id   ( core_inst.rs2_is_used_id ),
    .rs3_is_used_id   ( core_inst.rs3_is_used_id ),
    .rs1_or_fwd_id    ( core_inst.id_stage_inst.rs1_or_fwd_id ),
    .rs2_or_fwd_id    ( core_inst.id_stage_inst.rs2_or_fwd_id ),
    .rs3_or_fwd_id    ( core_inst.id_stage_inst.rs3_or_fwd_id ),
    .pc_id            ( core_inst.pc_id ),
    .pc_source_id     ( core_inst.pc_source_id ),
    .jump_target_id   ( core_inst.jump_target_id ),
    .mem_wen_id       ( core_inst.mem_wen_id ),
    
    // Input from EX stage
    .valid_ex           ( core_inst.valid_ex ),
    .stall_ex           ( core_inst.stall_ex ),
    .flush_ex           ( core_inst.flush_ex ),
    .trap_ex            ( core_inst.trap_ex ),
    .branch_target_ex   ( core_inst.branch_target_ex ),
    .branch_decision_ex ( core_inst.branch_decision_ex ),
    .csr_wdata_ex       ( core_inst.csr_inst.csr_wdata_actual ),
    .csr_rdata_ex       ( core_inst.csr_rdata_ex ),
    .csr_op_ex          ( core_inst.csr_op_ex ),
    
    // Input from MEM stage
    .valid_mem    ( core_inst.valid_mem ),
    .stall_mem    ( core_inst.stall_mem ),
    .flush_mem    ( core_inst.flush_mem ),
    .dmem_wdata_o ( core_inst.dmem_wdata_o ),
    .dmem_addr_o  ( core_inst.dmem_addr_o ),
    .dmem_wen_o   ( core_inst.dmem_wen_o ),
    .dmem_ben_o   ( core_inst.dmem_ben_o ),
    
    // Input from WB stage
    .flush_wb       ( core_inst.flush_wb ),
    .rd_addr_wb     ( core_inst.rd_addr_wb ),
    .rd_dst_bank_wb ( core_inst.rd_dst_bank_wb ),
    .reg_wen_wb     ( core_inst.reg_wen_wb ),
    .reg_wdata_wb   ( core_inst.reg_wdata_wb ),
    .mem_rdata_wb   ( core_inst.mem_rdata_wb ),
  
    .misa ( core_inst.csr_inst.misa ),
  
    `RVFI_CONN,
    
    .rvfi_frs1_addr     (  ),
    .rvfi_frs2_addr     (  ),
    .rvfi_frs3_addr     (  ),
    .rvfi_frd_addr      ( rvfi_frd_addr ),
    // .rvfi_frs1_rvalid   (  ),
    // .rvfi_frs2_rvalid   (  ),
    // .rvfi_frs3_rvalid   (  ),
    .rvfi_frd_wvalid    ( rvfi_frd_wvalid ),
    .rvfi_frs1_rdata    (  ),
    .rvfi_frs2_rdata    (  ),
    .rvfi_frs3_rdata    (  ),
    .rvfi_frd_wdata     ( rvfi_frd_wdata )
);
