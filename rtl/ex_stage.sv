module ex_stage import core_pkg::*; #(
    parameter bit ISA_M = 0,
    parameter bit ISA_C = 0,
    parameter bit ISA_F = 0
) (
    input  logic clk_i,
    input  logic rst_n_i,
    
    // Output to IF stage
    output pc_source_t  pc_source_ex_o,
    output logic [31:0] branch_target_ex_o,
    output logic        branch_decision_ex_o,
    
    // Input from ID stage
    input  alu_operation_t alu_operation_id_i,
    input  logic [ 4:0]    rd_addr_id_i,
    input  logic           mem_wen_id_i,
    input  data_type_t     mem_data_type_id_i,
    input  logic           mem_sign_extend_id_i,
    input  logic           reg_alu_wen_id_i,
    input  logic           reg_mem_wen_id_i,
    input  pc_source_t     pc_source_id_i,
    input  logic           is_branch_id_i,
    input  logic [31:0]    alu_operand_1_id_i,
    input  logic [31:0]    alu_operand_2_id_i,
    input  logic [31:0]    mem_wdata_id_i,
    input  logic [31:0]    branch_target_id_i,
    input  logic           valid_id_i,
    
    // Output to MEM stage
    output logic [ 4:0] rd_addr_ex_o,
    output logic [31:0] alu_result_ex_o,
    output logic        mem_wen_ex_o,
    output data_type_t  mem_data_type_ex_o,
    output logic        mem_sign_extend_ex_o,
    output logic [31:0] mem_wdata_ex_o,
    output logic        reg_alu_wen_ex_o,
    output logic        reg_mem_wen_ex_o,
    output logic        valid_ex_o,
    
    // Control inputs
    input  logic stall_ex_i,
    input  logic flush_mem_i
);

///////////////////////////////////////////////////////////////////////////////
/////////////////////////           EXECUTE           /////////////////////////
///////////////////////////////////////////////////////////////////////////////

alu_operation_t alu_operation_ex;
logic [31:0]    alu_operand_1_ex, alu_operand_2_ex;

logic is_branch_ex;

logic instr_addr_misaligned_ex;

// Pipeline registers ID->EX
always_ff @(posedge clk_i, negedge rst_n_i) begin
    if (!rst_n_i) begin
        rd_addr_ex_o         <= '0;
        alu_operation_ex     <= ALU_ADD;
        alu_operand_1_ex     <= '0;
        alu_operand_2_ex     <= '0;
        mem_wen_ex_o         <= '0;
        mem_data_type_ex_o   <= WORD;
        mem_sign_extend_ex_o <= '0;
        mem_wdata_ex_o       <= '0;
        reg_alu_wen_ex_o     <= '0;
        reg_mem_wen_ex_o     <= '0;
        pc_source_ex_o       <= PC_P_4;
        is_branch_ex         <= '0;
        branch_target_ex_o   <= '0;
    end else begin
        if (!stall_ex_i) begin
            if (valid_id_i) begin
                rd_addr_ex_o         <= rd_addr_id_i;
                alu_operation_ex     <= alu_operation_id_i;
                alu_operand_1_ex     <= alu_operand_1_id_i;
                alu_operand_2_ex     <= alu_operand_2_id_i;
                mem_wen_ex_o         <= mem_wen_id_i;
                mem_data_type_ex_o   <= mem_data_type_id_i;
                mem_sign_extend_ex_o <= mem_sign_extend_id_i;
                mem_wdata_ex_o       <= mem_wdata_id_i;
                reg_alu_wen_ex_o     <= reg_alu_wen_id_i;
                reg_mem_wen_ex_o     <= reg_mem_wen_id_i;
                pc_source_ex_o       <= pc_source_id_i;
                is_branch_ex         <= is_branch_id_i;
                branch_target_ex_o   <= branch_target_id_i;
            end
            // Insert bubble if previous stage wasn't valid
            else begin
                mem_wen_ex_o     <= '0;
                reg_alu_wen_ex_o <= '0;
                reg_mem_wen_ex_o <= '0;
                is_branch_ex     <= '0;
            end
        end
    end
end

alu #(
    .DWIDTH ( 32 )
) alu_inst (
	.res_o       ( alu_result_ex_o ), 
	.op1_i       ( alu_operand_1_ex ),
	.op2_i       ( alu_operand_2_ex ),
	.operation_i ( alu_operation_ex )
);

// Control signal for branches (this will invalidate IF and ID)
assign branch_decision_ex_o = is_branch_ex && alu_result_ex_o[0];

// Taken branch target misaligned exception
always_comb begin
    if (ISA_C) // No such exceptions if compressed instructions are allowed
        instr_addr_misaligned_ex = 1'b0;
    else // If no compressed instructions, target must be 4-byte aligned
        instr_addr_misaligned_ex = branch_target_ex_o[1] && branch_decision_ex_o;
end

// Resolve validness. Not valid implies inserting bubble
// assign valid_ex_o = !stall_ex_i && !flush_mem_i;
assign valid_ex_o = !stall_ex_i && !flush_mem_i && !instr_addr_misaligned_ex;

endmodule