module rvvi_wrapper #(
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
    
    // RVVI interface
    rvviTrace rvvi
);

// RVFI signals
`RVFI_WIRES

core #(
    .ISA_M(ISA_M),
    .ISA_C(ISA_C),
    .ISA_F(ISA_F)
) core_inst (
    .clk_i   ( clk_i ),
    .rst_n_i ( rst_n_i ),
    
    .dmem_rdata_i ( dmem_rdata_i ),
    .dmem_wdata_o ( dmem_wdata_o ),
    .dmem_addr_o  ( dmem_addr_o ),
    .dmem_wen_o   ( dmem_wen_o ),
    .dmem_ben_o   ( dmem_ben_o ),
    
    .imem_rdata_i ( imem_rdata_i ),
    .imem_addr_o  ( imem_addr_o )
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



// DRIVE RVVI

assign rvvi.clk = clk_i;
assign rvvi.valid[0][0] = rvfi_valid;
assign rvvi.order[0][0] = rvfi_order;

assign rvvi.insn[0][0] = rvfi_insn;
assign rvvi.trap[0][0] = rvfi_trap;
assign rvvi.debug_mode[0][0] = '0;

// Program counter
assign rvvi.pc_rdata[0][0] = rvfi_pc_rdata;

// X Registers
logic [31:0][31:0] x_wdata;   // X data value
logic [31:0]       x_wb   ;   // X data writeback (change) flag
always_comb begin
    foreach(rvvi.x_wdata[0][0][i]) begin
        // rvvi.x_wdata[0][0][i] = '0;
        // rvvi.x_wb[0][0][i]    = '0;
        x_wdata[i] = '0;
        x_wb[i]    = '0;
    end
    if (rvfi_rd_addr != '0) begin
        // rvvi.x_wdata[0][0][rvfi_rd_addr] = rvfi_rd_wdata;
        // rvvi.x_wb[0][0][rvfi_rd_addr]    = '1;
        x_wdata[rvfi_rd_addr] = rvfi_rd_wdata;
        x_wb[rvfi_rd_addr]    = '1;
    end
end
assign rvvi.x_wdata[0][0] = x_wdata;
assign rvvi.x_wb[0][0]    = x_wb;

// F Registers
// always_comb begin
//     foreach(rvvi.f_wdata[0][0][i]) begin
//         rvvi.f_wdata[0][0][i] <= '0;
//         rvvi.f_wb[0][0][i]    <= '0;
//     end
// end
assign rvvi.f_wdata[0][0] = '{default:'0};
assign rvvi.f_wb[0][0]    = '{default:'0};


// V Registers
// always_comb begin
//     foreach(rvvi.v_wdata[0][0][i]) begin
//         rvvi.v_wdata[0][0][i] <= '0;
//         rvvi.v_wb[0][0][i]    <= '0;
//     end
// end
assign rvvi.v_wdata[0][0] = '{default:'0};
assign rvvi.v_wb[0][0]    = '{default:'0};

// Control and Status Registers
// always_comb begin
//     foreach(rvvi.csr[0][0][i]) begin
//         rvvi.csr[0][0][i]    <= '0;
//         rvvi.csr_wb[0][0][i] <= '0;
//     end
// end
assign rvvi.csr[0][0]    = '{default:'0};
assign rvvi.csr_wb[0][0] = '{default:'0};

// Atomic Memory Control
assign rvvi.lrsc_cancel[0][0] = '0;

// Optional
assign rvvi.pc_wdata[0][0] = rvfi_pc_wdata;
assign rvvi.intr[0][0] = rvfi_intr;
assign rvvi.halt[0][0] = rvfi_halt;
assign rvvi.ixl[0][0] = rvfi_ixl;
assign rvvi.mode[0][0] = rvfi_mode;

endmodule

