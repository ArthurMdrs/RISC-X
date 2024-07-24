module controller import core_pkg::*; (
    // Data Hazards (forwarding)
    output forward_t fwd_op1_o,
    output forward_t fwd_op2_o,
    // Source/destiny general purpose registers
    input  logic [4:0] rs1_addr_id_i,
    input  logic [4:0] rs2_addr_id_i,
    input  logic [4:0] rd_addr_ex_i,
    input  logic [4:0] rd_addr_mem_i,
    input  logic [4:0] rd_addr_wb_i,
    // Write enables
    input  logic       reg_alu_wen_ex_i,
    input  logic       reg_alu_wen_mem_i,
    input  logic       reg_alu_wen_wb_i,
    input  logic       reg_mem_wen_mem_i,
    input  logic       reg_mem_wen_wb_i,
    
    // Data Hazards (stalling)
    output logic stall_if_o,
    output logic stall_id_o,
    output logic stall_ex_o,
    output logic stall_mem_o,
    input  logic reg_mem_wen_ex_i,
    
    // Control Hazards (flushing)
    output logic flush_id_o,
    output logic flush_ex_o,
    output logic flush_mem_o,
    output logic flush_wb_o,
    input  pc_source_t pc_source_id_i,
    input  logic       branch_decision_ex_i
    
);

logic rd_ex_is_rs1_id;
logic rd_mem_is_rs1_id;
logic rd_wb_is_rs1_id;

assign rd_ex_is_rs1_id  = (rd_addr_ex_i  == rs1_addr_id_i) && (rs1_addr_id_i != '0);
assign rd_mem_is_rs1_id = (rd_addr_mem_i == rs1_addr_id_i) && (rs1_addr_id_i != '0);
assign rd_wb_is_rs1_id  = (rd_addr_wb_i  == rs1_addr_id_i) && (rs1_addr_id_i != '0);

logic rd_ex_is_rs2_id;
logic rd_mem_is_rs2_id;
logic rd_wb_is_rs2_id;

assign rd_ex_is_rs2_id  = (rd_addr_ex_i  == rs2_addr_id_i) && (rs2_addr_id_i != '0);
assign rd_mem_is_rs2_id = (rd_addr_mem_i == rs2_addr_id_i) && (rs2_addr_id_i != '0);
assign rd_wb_is_rs2_id  = (rd_addr_wb_i  == rs2_addr_id_i) && (rs2_addr_id_i != '0);

// Resolve forwarding for rs1
always_comb begin
    fwd_op1_o = NO_FORWARD;
    if (rd_ex_is_rs1_id && reg_alu_wen_ex_i) begin
        fwd_op1_o = FWD_EX_ALU_RES_TO_ID;
    end
    else if (rd_mem_is_rs1_id && (reg_alu_wen_mem_i || reg_mem_wen_mem_i)) begin
        if (reg_alu_wen_mem_i)
            fwd_op1_o = FWD_MEM_ALU_RES_TO_ID;
        else if (reg_mem_wen_mem_i)
            fwd_op1_o = FWD_MEM_RDATA_TO_ID;
    end
    else if (rd_wb_is_rs1_id && (reg_alu_wen_wb_i || reg_mem_wen_wb_i)) begin
        if (reg_alu_wen_wb_i)
            fwd_op1_o = FWD_WB_ALU_RES_TO_ID;
        else if (reg_mem_wen_wb_i)
            fwd_op1_o = FWD_WB_RDATA_TO_ID;
    end
end

// Resolve forwarding for rs2
always_comb begin
    fwd_op2_o = NO_FORWARD;
    if (rd_ex_is_rs2_id && reg_alu_wen_ex_i) begin
        fwd_op2_o = FWD_EX_ALU_RES_TO_ID;
    end
    else if (rd_mem_is_rs2_id && (reg_alu_wen_mem_i || reg_mem_wen_mem_i)) begin
        if (reg_alu_wen_mem_i)
            fwd_op2_o = FWD_MEM_ALU_RES_TO_ID;
        else if (reg_mem_wen_mem_i)
            fwd_op2_o = FWD_MEM_RDATA_TO_ID;
    end
    else if (rd_wb_is_rs2_id && (reg_alu_wen_wb_i || reg_mem_wen_wb_i)) begin
        if (reg_alu_wen_wb_i)
            fwd_op2_o = FWD_WB_ALU_RES_TO_ID;
        else if (reg_mem_wen_wb_i)
            fwd_op2_o = FWD_WB_RDATA_TO_ID;
    end
end

// Resolve stalls
always_comb begin
    stall_id_o = 1'b0;
    if (reg_mem_wen_ex_i)
        if(rd_ex_is_rs1_id || rd_ex_is_rs2_id)
            stall_id_o = 1'b1;
    
    stall_if_o = stall_id_o;
    stall_ex_o = 1'b0;
    stall_mem_o = 1'b0;
end

logic id_is_jump;
assign id_is_jump = pc_source_id_i == PC_JAL || pc_source_id_i == PC_JALR;


// Resolve flushing
always_comb begin
    flush_id_o = branch_decision_ex_i || id_is_jump;
    flush_ex_o = branch_decision_ex_i;
    flush_mem_o = 1'b0;
    flush_wb_o = 1'b0;
end

endmodule
