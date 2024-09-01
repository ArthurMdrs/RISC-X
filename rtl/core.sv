/*
    Author: Pedro Medeiros (pedromedeiros.egnr@gmail.com)
    
    This is a very simple pipelined RISC-V core.
    RV32I ISA, in-order, 5 pipeline stages (Instruction Fetch, Instruction Decode, 
    Execution, Memory Access, Write Back).
*/

module core #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,

    // Interface with data memory
    input  logic [31:0] dmem_rdata_i,
    output logic [31:0] dmem_wdata_o,
    output logic [31:0] dmem_addr_o,
    output logic        dmem_wen_o,
    output logic  [3:0] dmem_ben_o,

    // Interface with instruction memory
    input  logic [31:0] imem_rdata_i,
    output logic [31:0] imem_addr_o,
    
    // Hart ID, defined by system
    input  logic [31:0] hartid_i,
    // mtvec initial address, defined by system
    input  logic [23:0] mtvec_i, // 24 upper bits, 256-byte aligned
    // Boot addr (first fetch)
    input  logic [29:0] boot_addr_i // 30 upper bits, word aligned
);

import core_pkg::*;

// Program Counter, Instruction and pipeline control signals
logic [31:0] pc_if, pc_id, pc_ex;
logic [31:0] instr_if;
logic        valid_if, valid_id, valid_ex, valid_mem;
// logic        ready_if, ready_id, ready_ex, ready_mem, ready_wb;
logic        stall_if, stall_id, stall_ex, stall_mem;
logic        flush_id, flush_ex, flush_mem, flush_wb;
logic        is_compressed_if;

// Source and destiny registers from register file
logic [4:0] rs1_addr_id, rs2_addr_id, rs3_addr_id;
logic [4:0] rd_addr_id, rd_addr_ex, rd_addr_mem, rd_addr_wb;

// ALU control signals, operands and result
alu_operation_t    alu_operation_id;
logic [31:0]       alu_operand_1_id;
logic [31:0]       alu_operand_2_id;
logic [31:0]       alu_result_ex, alu_result_mem, alu_result_wb;
forward_t          fwd_op1_id, fwd_op2_id, fwd_op3_id;
alu_result_mux_t   alu_result_mux_id;

// Memory access control signals, write data and read data
logic        mem_wen_id, mem_wen_ex, mem_wen_mem;
data_type_t  mem_data_type_id, mem_data_type_ex, mem_data_type_mem;
logic        mem_sign_extend_id, mem_sign_extend_ex, mem_sign_extend_mem;
logic [31:0] mem_wdata_id, mem_wdata_ex;//, mem_wdata_mem;
logic [31:0] mem_rdata_mem, mem_rdata_wb;

// Register file write enables and write data (distinguish between writes from ALU or from loads)
logic        reg_alu_wen_id, reg_alu_wen_ex, reg_alu_wen_mem, reg_alu_wen_wb;
logic        reg_mem_wen_id, reg_mem_wen_ex, reg_mem_wen_mem, reg_mem_wen_wb;
logic        reg_wen_wb;
logic [31:0] reg_wdata_wb;

// Program Counter control and branch target
pc_source_t  pc_source_id, pc_source_ex; 
logic        is_branch_id;
logic [31:0] branch_target_id, branch_target_ex;
logic [31:0] jump_target_id;
logic        branch_decision_ex;

// Indicator of traps
logic trap_id, trap_ex;
logic illegal_instr_id;
logic instr_addr_misaligned_id;
// logic instr_addr_misaligned_ex;
logic is_mret_id;

// CSR signals
logic           csr_access_id, csr_access_ex;
csr_operation_t csr_op_id, csr_op_ex;
logic [31:0]    csr_wdata_ex;
logic [31:0]    csr_rdata_ex;
csr_addr_t      csr_addr_ex;
logic [31:0]    mtvec, mepc;
logic           save_pc_id, save_pc_ex;
logic [ 4:0]    exception_cause;

// FPU signals
logic [2:0] fpu_rnd_mode_id;
logic [3:0] fpu_op_id;
logic       fpu_op_mod_id;
logic       fpu_req_id, fpu_gnt_id;
logic       fpu_busy_ex;
logic [4:0] csr_fpu_flags_ex;



///////////////////////////////////////////////////////////////////////////////
///////////////////////        INSTRUCTION FETCH        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

if_stage if_stage_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    .boot_addr_i ( boot_addr_i ),
    
    // Interface with instruction memory
    .imem_rdata_i ( imem_rdata_i ),
    .imem_addr_o  ( imem_addr_o ),
    
    // Output to ID stage
    .pc_if_o            ( pc_if ),
    .instr_if_o         ( instr_if ),
    .valid_if_o         ( valid_if ),
    .is_compressed_if_o ( is_compressed_if ),
    
    // Control inputs
    .stall_if_i (stall_if),
    
    // Trap handling
    .trap_id_i ( trap_id ),
    .trap_ex_i ( trap_ex ),
    .is_mret_i ( is_mret_id ),
    .mtvec_i   ( mtvec ),
    .mepc_i    ( mepc ),
    
    // Signals for the PC controller
    .valid_id_i           ( valid_id ),
    .valid_ex_i           ( valid_ex ),
    .jump_target_id_i     ( jump_target_id ), 
    .branch_target_ex_i   ( branch_target_ex ), 
    .branch_decision_ex_i ( branch_decision_ex ),
    .pc_source_id_i       ( pc_source_id ),
    .pc_source_ex_i       ( pc_source_ex )
);



///////////////////////////////////////////////////////////////////////////////
//////////////////////        INSTRUCTION DECODE        ///////////////////////
///////////////////////////////////////////////////////////////////////////////

id_stage #(
    .ISA_M ( ISA_M ),
    .ISA_C ( ISA_C ),
    .ISA_F ( ISA_F )
) id_stage_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Input from IF stage
    .pc_if_i            ( pc_if ),
    .instr_if_i         ( instr_if ),
    .valid_if_i         ( valid_if ),
    .is_compressed_if_i ( is_compressed_if ),
    
    // Output to IF stage
    .jump_target_id_o ( jump_target_id ),
    .trap_id_o        ( trap_id ),
    
    // Output to EX stage
    .alu_operation_id_o     ( alu_operation_id ),
    .alu_result_mux_id_o    ( alu_result_mux_id ),
    .rd_addr_id_o           ( rd_addr_id ),
    .mem_wen_id_o           ( mem_wen_id ),
    .mem_data_type_id_o     ( mem_data_type_id ),
    .mem_sign_extend_id_o   ( mem_sign_extend_id ),
    .reg_alu_wen_id_o       ( reg_alu_wen_id ),
    .reg_mem_wen_id_o       ( reg_mem_wen_id ),
    .pc_source_id_o         ( pc_source_id ),
    .pc_id_o                ( pc_id ),
    .is_branch_id_o         ( is_branch_id ),
    .alu_operand_1_id_o     ( alu_operand_1_id ),
    .alu_operand_2_id_o     ( alu_operand_2_id ),
    .mem_wdata_id_o         ( mem_wdata_id ),
    .branch_target_id_o     ( branch_target_id ),
    .valid_id_o             ( valid_id ),
    
    // Input from WB stage
    .reg_wdata_wb_i ( reg_wdata_wb ),
    .rd_addr_wb_i   ( rd_addr_wb ),
    .reg_wen_wb_i   ( reg_wen_wb ),
    
    // Output to controller
    .rs1_addr_id_o ( rs1_addr_id ),
    .rs2_addr_id_o ( rs2_addr_id ),
    .rs3_addr_id_o ( rs3_addr_id ),
    .illegal_instr_id_o ( illegal_instr_id ),
    .instr_addr_misaligned_id_o ( instr_addr_misaligned_id ),
    .is_mret_id_o ( is_mret_id ),
    
    // Output to CSRs
    .csr_access_id_o ( csr_access_id ),
    .csr_op_id_o     ( csr_op_id ),
    
    // Control inputs
    .stall_id_i ( stall_id ),
    .flush_id_i (flush_id),
    .branch_decision_ex_i      ( branch_decision_ex ),
    
    // Inputs for forwarding
    .fwd_op1_id_i       ( fwd_op1_id ),
    .fwd_op2_id_i       ( fwd_op2_id ),
    .alu_result_ex_i    ( alu_result_ex ),
    .alu_result_mem_i   ( alu_result_mem ),
    .mem_rdata_mem_i    ( mem_rdata_mem ),
    .alu_result_wb_i    ( alu_result_wb ),
    .mem_rdata_wb_i     ( mem_rdata_wb ),
    .csr_rdata_ex_i     ( csr_rdata_ex ),
    
    // FPU signals
    .fpu_rnd_mode_id_o ( fpu_rnd_mode_id ),
    .fpu_op_id_o       ( fpu_op_id ),
    .fpu_op_mod_id_o   ( fpu_op_mod_id ),
    .fpu_req_id_o      ( fpu_req_id ),
    
    .rs1_src_bank_id_o ( rs1_src_bank_id ),
    .rs2_src_bank_id_o ( rs2_src_bank_id ),
    .rs3_src_bank_id_o ( rs3_src_bank_id ),
    .rd_dst_bank_id_o  ( rd_dst_bank_id )
);



///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

ex_stage #(
    .ISA_M ( ISA_M ),
    .ISA_C ( ISA_C ),
    .ISA_F ( ISA_F )
) ex_stage_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Output to IF stage
    .pc_source_ex_o       ( pc_source_ex ),
    .branch_target_ex_o   ( branch_target_ex ),
    .branch_decision_ex_o ( branch_decision_ex ),
    .trap_ex_o            ( trap_ex ),
    
    // Input from ID stage
    .alu_operation_id_i     ( alu_operation_id ),
    .alu_result_mux_id_i    ( alu_result_mux_id ),
    .rd_addr_id_i           ( rd_addr_id ),
    .mem_wen_id_i           ( mem_wen_id ),
    .mem_data_type_id_i     ( mem_data_type_id ),
    .mem_sign_extend_id_i   ( mem_sign_extend_id ),
    .reg_alu_wen_id_i       ( reg_alu_wen_id ),
    .reg_mem_wen_id_i       ( reg_mem_wen_id ),
    .pc_id_i                ( pc_id ),
    .pc_source_id_i         ( pc_source_id ),
    .is_branch_id_i         ( is_branch_id ),
    .alu_operand_1_id_i     ( alu_operand_1_id ),
    .alu_operand_2_id_i     ( alu_operand_2_id ),
    .mem_wdata_id_i         ( mem_wdata_id ),
    .branch_target_id_i     ( branch_target_id ),
    .valid_id_i             ( valid_id ),
    .csr_access_id_i        ( csr_access_id ),
    .csr_op_id_i            ( csr_op_id ),
    
    // Output to MEM stage
    .rd_addr_ex_o         ( rd_addr_ex ),
    .alu_result_ex_o      ( alu_result_ex ),
    .mem_wen_ex_o         ( mem_wen_ex ),
    .mem_data_type_ex_o   ( mem_data_type_ex ),
    .mem_sign_extend_ex_o ( mem_sign_extend_ex ),
    .mem_wdata_ex_o       ( mem_wdata_ex ),
    .reg_alu_wen_ex_o     ( reg_alu_wen_ex ),
    .reg_mem_wen_ex_o     ( reg_mem_wen_ex ),
    .valid_ex_o           ( valid_ex ),
    
    // Output to controller
    // .instr_addr_misaligned_ex_o ( instr_addr_misaligned_ex ),
    
    // Output to CSRs
    .pc_ex_o            ( pc_ex ),
    .csr_addr_ex_o      ( csr_addr_ex ),
    .csr_wdata_ex_o     ( csr_wdata_ex ),
    .csr_op_ex_o        ( csr_op_ex ),
    .csr_access_ex_o    ( csr_access_ex ),
    .csr_fpu_flags_ex_o ( csr_fpu_flags_ex ),
    
    // Input from CSRs
    .csr_access_ex_i      ( csr_access_ex ),
    .csr_rdata_ex_i       ( csr_rdata_ex ),
    
    // Control inputs
    .stall_ex_i ( stall_ex ),
    .flush_ex_i ( flush_ex ),
    
    // FPU signals
    .fpu_rnd_mode_id_i ( fpu_rnd_mode_id ),
    .fpu_op_id_i       ( fpu_op_id ),
    .fpu_op_mod_id_i   ( fpu_op_mod_id ),
    .fpu_req_id_i      ( fpu_req_id ),
    .fpu_gnt_id_o      ( fpu_gnt_id ),
    .fpu_busy_ex_o     ( fpu_busy_ex )
    
    // .rs1_src_bank_id_i ( rs1_src_bank_id ),
    // .rs2_src_bank_id_i ( rs2_src_bank_id ),
    // .rs3_src_bank_id_i ( rs3_src_bank_id ),
    // .rd_dst_bank_id_i  ( rd_dst_bank_id )
);



///////////////////////////////////////////////////////////////////////////////
///////////////////////          MEMORY ACCESS          ///////////////////////
///////////////////////////////////////////////////////////////////////////////

mem_stage mem_stage_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),

    // Interface with data memory
    .dmem_rdata_i ( dmem_rdata_i ),
    .dmem_wdata_o ( dmem_wdata_o ),
    .dmem_addr_o  ( dmem_addr_o ),
    .dmem_wen_o   ( dmem_wen_o ),
    .dmem_ben_o   ( dmem_ben_o ),
    
    // Input from EX stage
    .rd_addr_ex_i         ( rd_addr_ex ),
    .alu_result_ex_i      ( alu_result_ex ),
    .mem_wen_ex_i         ( mem_wen_ex ),
    .mem_data_type_ex_i   ( mem_data_type_ex ),
    .mem_sign_extend_ex_i ( mem_sign_extend_ex ),
    .mem_wdata_ex_i       ( mem_wdata_ex ),
    .reg_alu_wen_ex_i     ( reg_alu_wen_ex ),
    .reg_mem_wen_ex_i     ( reg_mem_wen_ex ),
    .valid_ex_i           ( valid_ex ),
    
    // Output to WB stage
    .rd_addr_mem_o     ( rd_addr_mem ),
    .alu_result_mem_o  ( alu_result_mem ),
    .mem_rdata_mem_o   ( mem_rdata_mem ),
    .reg_alu_wen_mem_o ( reg_alu_wen_mem ),
    .reg_mem_wen_mem_o ( reg_mem_wen_mem ),
    .valid_mem_o       ( valid_mem ),
    
    // Control inputs
    .stall_mem_i ( stall_mem ),
    .flush_mem_i ( flush_mem )
);



///////////////////////////////////////////////////////////////////////////////
////////////////////////          WRITE BACK          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

wb_stage wb_stage_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Input from MEM stage
    .rd_addr_mem_i     ( rd_addr_mem ),
    .alu_result_mem_i  ( alu_result_mem ),
    .mem_rdata_mem_i   ( mem_rdata_mem ),
    .reg_alu_wen_mem_i ( reg_alu_wen_mem ),
    .reg_mem_wen_mem_i ( reg_mem_wen_mem ),
    .valid_mem_i       ( valid_mem ),
    
    // Output to register file
    .reg_wdata_wb_o ( reg_wdata_wb ),
    .reg_wen_wb_o   ( reg_wen_wb ),
    
    // Output for forwarding
    .rd_addr_wb_o     ( rd_addr_wb ),
    .alu_result_wb_o  ( alu_result_wb ),
    .mem_rdata_wb_o   ( mem_rdata_wb ),
    .reg_alu_wen_wb_o ( reg_alu_wen_wb ),
    .reg_mem_wen_wb_o ( reg_mem_wen_wb ),
    
    // Control inputs
    .flush_wb_i  ( flush_wb )
);



///////////////////////////////////////////////////////////////////////////////
////////////////////       CONTROL/STATUS REGISTERS       /////////////////////
///////////////////////////////////////////////////////////////////////////////

csr #(
    .ISA_M ( ISA_M ),
    .ISA_C ( ISA_C ),
    .ISA_F ( ISA_F )
) csr_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Ports for CSR read/modify instructions
    .csr_addr_i  ( csr_addr_ex ),
    .csr_wdata_i ( csr_wdata_ex ),
    .csr_op_i    ( csr_op_ex ),
    .csr_rdata_o ( csr_rdata_ex ),
    
    // Initial values of CSRs
    .hartid_i ( hartid_i ),
    .mtvec_i  ( mtvec_i ),
    
    // Output some CSRs
    .mtvec_o ( mtvec ),
    .mepc_o  ( mepc ),
    
    // Trap handling
    .save_pc_id_i ( save_pc_id ),
    .save_pc_ex_i ( save_pc_ex ),
    .pc_id_i      ( pc_id ),
    .pc_ex_i      ( pc_ex ),
    .exception_cause_i ( exception_cause ),
    
    // Floating-point ports
    .fflags_i   ( csr_fpu_flags_ex ),
    .fflag_we_i ( 1'b0 ),
    .fregs_we_i ( 1'b0 ),
    .frm_o      (  )
);



///////////////////////////////////////////////////////////////////////////////
////////////////////////          CONTROLLER          /////////////////////////
///////////////////////////////////////////////////////////////////////////////

controller controller_inst (
    // Data Hazards (forwarding)
    .fwd_op1_o ( fwd_op1_id ),
    .fwd_op2_o ( fwd_op2_id ),
    .fwd_op3_o ( fwd_op3_id ),
    // Source/destiny general purpose registers
    .rs1_addr_id_i     ( rs1_addr_id ),
    .rs2_addr_id_i     ( rs2_addr_id ),
    .rs3_addr_id_i     ( rs3_addr_id ),
    .rd_addr_ex_i      ( rd_addr_ex ),
    .rd_addr_mem_i     ( rd_addr_mem ),
    .rd_addr_wb_i      ( rd_addr_wb ),
    // Write enables
    .reg_alu_wen_ex_i  ( reg_alu_wen_ex ),
    .reg_alu_wen_mem_i ( reg_alu_wen_mem ),
    .reg_alu_wen_wb_i  ( reg_alu_wen_wb ),
    .reg_mem_wen_ex_i  ( reg_mem_wen_ex ),
    .reg_mem_wen_mem_i ( reg_mem_wen_mem ),
    .reg_mem_wen_wb_i  ( reg_mem_wen_wb ),
    
    // Data Hazards (stalling)
    .stall_if_o    ( stall_if ),
    .stall_id_o    ( stall_id ),
    .stall_ex_o    ( stall_ex ),
    .stall_mem_o   ( stall_mem ),
    .fpu_req_id_i  ( fpu_req_id ),
    .fpu_gnt_id_i  ( fpu_gnt_id ),
    .fpu_busy_ex_i ( fpu_busy_ex ),
    
    // Control Hazards (flushing)
    .flush_id_o  ( flush_id ),
    .flush_ex_o  ( flush_ex ),
    .flush_mem_o ( flush_mem ),
    .flush_wb_o  ( flush_wb ),
    .pc_source_id_i       ( pc_source_id ),
    .branch_decision_ex_i ( branch_decision_ex ),
    .trap_id_i ( trap_id ),
    .trap_ex_i ( trap_ex ),
    
    // Trap handling
    .save_pc_id_o      ( save_pc_id ),
    .save_pc_ex_o      ( save_pc_ex ),
    .illegal_instr_id_i ( illegal_instr_id ),
    .instr_addr_misaligned_id_i ( instr_addr_misaligned_id ),
    // .instr_addr_misaligned_ex_i ( instr_addr_misaligned_ex ),
    .is_mret_id_i      ( is_mret_id ),
    .exception_cause_o ( exception_cause )

    // // FPU Controler
    // .fflag_i(fflags_csr),
    // .fflag_we_i(fflags_we),
    // .fregs_we_i(fregs_we),
    // .frm_o(frm_csr)
);

endmodule