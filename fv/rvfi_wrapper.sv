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
    
////////////////////    PORT LIST - END    ////////////////////
    
// Tie-offs
assign clk_i   = clock;
assign rst_n_i = !reset;

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
    .imem_addr_o  ( imem_addr )
);

rvfi rvfi_inst (
    .clk_i ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    // Input from IF stage
    .valid_if ( core_inst.valid_if ),
    .pc_if ( core_inst.pc_if ),
    
    // Input from ID stage
    .valid_id ( core_inst.valid_id ),
    .stall_id ( core_inst.stall_id ),
    
    .instr_id ( core_inst.id_stage_inst.instr_id ),
    .illegal_instr_id ( core_inst.id_stage_inst.illegal_instr_id ),
    .alu_source_1_id ( core_inst.id_stage_inst.alu_source_1_id ),
    .alu_source_2_id ( core_inst.id_stage_inst.alu_source_2_id ),
    
    .rs1_addr_id ( core_inst.rs1_addr_id ),
    .rs2_addr_id ( core_inst.rs2_addr_id ),
    
    .rs1_or_fwd_id ( core_inst.id_stage_inst.rs1_or_fwd_id ),
    .rs2_or_fwd_id ( core_inst.id_stage_inst.rs2_or_fwd_id ),
    .pc_id ( core_inst.id_stage_inst.pc_id ),
    .pc_source_id ( core_inst.pc_source_id ),
    .jump_target_id ( core_inst.jump_target_id ),
    .mem_wen_id ( core_inst.mem_wen_id ),
    
    // Input from EX stage
    .valid_ex ( core_inst.valid_ex ),
    .stall_ex ( core_inst.stall_ex ),
    .flush_ex ( core_inst.flush_ex ),
    .branch_target_ex ( core_inst.branch_target_ex ),
    .branch_decision_ex ( core_inst.branch_decision_ex ),
    
    // Input from MEM stage
    .valid_mem ( core_inst.valid_mem ),
    .stall_mem ( core_inst.stall_mem ),
    .dmem_wdata_o ( core_inst.dmem_wdata_o ),
    .dmem_addr_o ( core_inst.dmem_addr_o ),
    .dmem_wen_o ( core_inst.dmem_wen_o ),
    .dmem_ben_o ( core_inst.dmem_ben_o ),
    
    // Input from WB stage
    .rd_addr_wb ( core_inst.rd_addr_wb ),
    .reg_wen_wb ( core_inst.reg_wen_wb ),
    .reg_wdata_wb ( core_inst.reg_wdata_wb ),
    .mem_rdata_wb ( core_inst.mem_rdata_wb ),
  
    `RVFI_CONN
);
    
// `ifdef CV32P_PC_FWD
// `endif

endmodule

