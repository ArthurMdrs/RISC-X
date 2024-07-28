module rvfi_wrapper (
    input logic clock,
    input logic reset
    ,
    `RVFI_OUTPUTS
);
    
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
    
// Tie-offs
assign clk_i   = clock;
assign rst_n_i = !reset;

assign hartid    = 32'h0000_0000;
assign mtvec     = 24'h0000_80;
assign boot_addr = 30'h0000_0c00; // Equivalent to 32'b0000_3000;

`default_nettype none
core core_inst (
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

// rvfi rvfi_inst (
//     .clk_i   ( clk_i ),
//     .rst_n_i ( rst_n_i ),
    
//     // Input from IF stage
//     .valid_if    ( core_inst.valid_if ),
//     .stall_if    ( core_inst.stall_if ),
//     .pc_if       ( core_inst.pc_if ),
//     .next_pc_mux ( core_inst.if_stage_inst.pc_constroller_inst.next_pc_mux ),
    
//     // Input from ID stage
//     .valid_id         ( core_inst.valid_id ),
//     .stall_id         ( core_inst.stall_id ),
//     .flush_id         ( core_inst.flush_id ),
//     .trap_id          ( core_inst.trap_id ),
//     .instr_id         ( core_inst.id_stage_inst.instr_id ),
//     .illegal_instr_id ( core_inst.illegal_instr_id ),
//     .alu_source_1_id  ( core_inst.id_stage_inst.alu_source_1_id ),
//     .alu_source_2_id  ( core_inst.id_stage_inst.alu_source_2_id ),
//     .rs1_addr_id      ( core_inst.rs1_addr_id ),
//     .rs2_addr_id      ( core_inst.rs2_addr_id ),
//     .rs1_or_fwd_id    ( core_inst.id_stage_inst.rs1_or_fwd_id ),
//     .rs2_or_fwd_id    ( core_inst.id_stage_inst.rs2_or_fwd_id ),
//     .pc_id            ( core_inst.pc_id ),
//     .pc_source_id     ( core_inst.pc_source_id ),
//     .jump_target_id   ( core_inst.jump_target_id ),
//     .mem_wen_id       ( core_inst.mem_wen_id ),
    
//     // Input from EX stage
//     .valid_ex           ( core_inst.valid_ex ),
//     .stall_ex           ( core_inst.stall_ex ),
//     .flush_ex           ( core_inst.flush_ex ),
//     .trap_ex            ( core_inst.trap_ex ),
//     .branch_target_ex   ( core_inst.branch_target_ex ),
//     .branch_decision_ex ( core_inst.branch_decision_ex ),
//     .csr_wdata_ex       ( core_inst.csr_inst.csr_wdata_actual ),
//     .csr_rdata_ex       ( core_inst.csr_rdata_ex ),
    
//     // Input from MEM stage
//     .valid_mem    ( core_inst.valid_mem ),
//     .stall_mem    ( core_inst.stall_mem ),
//     .flush_mem    ( core_inst.flush_mem ),
//     .dmem_wdata_o ( core_inst.dmem_wdata_o ),
//     .dmem_addr_o  ( core_inst.dmem_addr_o ),
//     .dmem_wen_o   ( core_inst.dmem_wen_o ),
//     .dmem_ben_o   ( core_inst.dmem_ben_o ),
    
//     // Input from WB stage
//     .flush_wb     ( core_inst.flush_wb ),
//     .rd_addr_wb   ( core_inst.rd_addr_wb ),
//     .reg_wen_wb   ( core_inst.reg_wen_wb ),
//     .reg_wdata_wb ( core_inst.reg_wdata_wb ),
//     .mem_rdata_wb ( core_inst.mem_rdata_wb ),
  
//     .misa ( core_inst.csr_inst.misa ),
  
//     `RVFI_CONN
// );

`include "rvfi_inst.sv"

endmodule

